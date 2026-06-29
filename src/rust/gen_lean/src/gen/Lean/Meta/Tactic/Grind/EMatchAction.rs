// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.EMatchAction
// Imports: Lean.Meta.Tactic.Grind.Intro Lean.Util.ParamMinimizer Lean.Meta.Tactic.Grind.EMatch Lean.Meta.Tactic.Grind.EMatchTheoremParam Lean.Meta.Tactic.Grind.EMatchTheoremPtr Lean.Meta.Tactic.Grind.MarkNestedSubsingletons
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_SepArray_ofElems;
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node1, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_lt;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasMVar, l_Lean_mkMVar};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Eqns::l_Lean_Meta_isEqnThm_x3f___redArg;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Action::{
    l_Lean_Meta_Grind_Action_andThen, l_Lean_Meta_Grind_Action_checkSeqAt,
    l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Anchor::{
    l_Lean_Meta_Grind_getAnchor, l_Lean_Meta_Grind_mkAnchorSyntax___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatch::{
    initialize_Lean_Meta_Tactic_Grind_EMatch, l_Lean_Meta_Grind_EMatch_isTheoremInstanceProof_x3f,
    l_Lean_Meta_Grind_ematch_x27, runtime_initialize_Lean_Meta_Tactic_Grind_EMatch,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheoremParam::{
    initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam,
    l_Lean_Meta_Grind_getNumDigitsForLocalTheoremAnchors,
    l_Lean_Meta_Grind_globalDeclToInstantiateParamSyntax,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheoremPtr::{
    initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr,
    l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1,
    l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1,
    runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Extension::{
    l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq,
    l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash,
    l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Intro::{
    initialize_Lean_Meta_Tactic_Grind_Intro, l_Lean_Meta_Grind_Action_assertAll___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Intro,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MarkNestedSubsingletons::{
    initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons,
    l_Lean_Meta_Grind_isMarkedSubsingletonApp,
    runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Theorems::l_Lean_Meta_Grind_Origin_key;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_getConfig___redArg, l_Lean_Meta_Grind_isMatchEqLikeDeclName,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::ParamMinimizer::{
    initialize_Lean_Util_ParamMinimizer, runtime_initialize_Lean_Util_ParamMinimizer,
};
use crate::ffi::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::{lean_array_fset, lean_array_set};
use crate::ffi::lean_nat_shiftr;
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_infer_type;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0: u64 = 0;
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 104, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__4_value) as *mut crate::leanh::LeanObject,4493657671338864619 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__2_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__3_value) as *mut crate::leanh::LeanObject,3168557723425139092 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,12928201877799427862 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__7_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 110, 108, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__11_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__12_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__13_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__14_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 112, 112, 114, 111, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___closed__0_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 44, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 110, 100, 101, 120, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Action_instantiate_x27___lam__1___closed__0_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 96, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116,
        101, 96, 32, 116, 97, 99, 116, 105, 99, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32,
        111, 112, 116, 105, 109, 105, 122, 101, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_Action_instantiate_x27___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instantiate_x27___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___closed__1_value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 15, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_instantiate_x27___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Grind_Action_instantiate_x27___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instantiate_x27___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_instantiate___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Action_instantiate___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Action_instantiate___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_instantiate___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3_spec__6___redArg(
    mut v_a_3514_: *mut crate::leanh::LeanObject,
    mut v_x_3515_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3516_: u8 = 0;
    let mut v_key_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3520_: u8 = 0;
    let mut v_fst_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: u8 = 0;
    let mut v___x_3529_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3515_) == 0 {
                    v___x_3516_ = 0;
                    return v___x_3516_;
                } else {
                    v_key_3517_ = crate::leanh::lean_ctor_get(v_x_3515_, 0);
                    v_tail_3518_ = crate::leanh::lean_ctor_get(v_x_3515_, 2);
                    v_fst_3522_ = crate::leanh::lean_ctor_get(v_key_3517_, 0);
                    v_snd_3523_ = crate::leanh::lean_ctor_get(v_key_3517_, 1);
                    v_fst_3524_ = crate::leanh::lean_ctor_get(v_a_3514_, 0);
                    v_snd_3525_ = crate::leanh::lean_ctor_get(v_a_3514_, 1);
                    v___x_3526_ = l_Lean_Meta_Grind_Origin_key(v_fst_3522_);
                    v___x_3527_ = l_Lean_Meta_Grind_Origin_key(v_fst_3524_);
                    v___x_3528_ = lean_name_eq(v___x_3526_, v___x_3527_);
                    crate::leanh::lean_dec(v___x_3527_);
                    crate::leanh::lean_dec(v___x_3526_);
                    if v___x_3528_ == 0 {
                        v___y_3520_ = v___x_3528_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3529_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(
                            v_snd_3523_,
                            v_snd_3525_,
                        );
                        v___y_3520_ = v___x_3529_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3520_ == 0 {
                    v_x_3515_ = v_tail_3518_;
                    state = 0;
                    continue;
                } else {
                    return v___y_3520_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3_spec__6___redArg___boxed(
    mut v_a_3530_: *mut crate::leanh::LeanObject,
    mut v_x_3531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3532_: u8 = 0;
    let mut v_r_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3532_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3_spec__6___redArg(v_a_3530_, v_x_3531_);
    crate::leanh::lean_dec(v_x_3531_);
    crate::leanh::lean_dec_ref(v_a_3530_);
    v_r_3533_ = crate::leanh::lean_box((v_res_3532_) as usize);
    return v_r_3533_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0()
-> u64 {
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: u64 = 0;
    v___x_3534_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_3535_ = lean_uint64_of_nat(v___x_3534_);
    return v___x_3535_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg(
    mut v_x_3536_: *mut crate::leanh::LeanObject,
    mut v_x_3537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3543_: u8 = 0;
    let mut v_fst_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3548_: u64 = 0;
    let mut v___x_3549_: u64 = 0;
    let mut v___x_3550_: u64 = 0;
    let mut v___x_3551_: u64 = 0;
    let mut v___x_3552_: u64 = 0;
    let mut v_fold_3553_: u64 = 0;
    let mut v___x_3554_: u64 = 0;
    let mut v___x_3555_: u64 = 0;
    let mut v___x_3556_: u64 = 0;
    let mut v___x_3557_: usize = 0;
    let mut v___x_3558_: usize = 0;
    let mut v___x_3559_: usize = 0;
    let mut v___x_3560_: usize = 0;
    let mut v___x_3561_: usize = 0;
    let mut v___x_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: u64 = 0;
    let mut v_hash_3570_: u64 = 0;
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3537_) == 0 {
                    return v_x_3536_;
                } else {
                    v_key_3538_ = crate::leanh::lean_ctor_get(v_x_3537_, 0);
                    v_value_3539_ = crate::leanh::lean_ctor_get(v_x_3537_, 1);
                    v_tail_3540_ = crate::leanh::lean_ctor_get(v_x_3537_, 2);
                    v_isSharedCheck_3571_ = (!crate::leanh::lean_is_exclusive(v_x_3537_)) as u8;
                    if v_isSharedCheck_3571_ == 0 {
                        v___x_3542_ = v_x_3537_;
                        v_isShared_3543_ = v_isSharedCheck_3571_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3540_);
                        crate::leanh::lean_inc(v_value_3539_);
                        crate::leanh::lean_inc(v_key_3538_);
                        crate::leanh::lean_dec(v_x_3537_);
                        v___x_3542_ = crate::leanh::lean_box(0);
                        v_isShared_3543_ = v_isSharedCheck_3571_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3544_ = crate::leanh::lean_ctor_get(v_key_3538_, 0);
                v_snd_3545_ = crate::leanh::lean_ctor_get(v_key_3538_, 1);
                v___x_3546_ = lean_array_get_size(v_x_3536_);
                v___x_3568_ = l_Lean_Meta_Grind_Origin_key(v_fst_3544_);
                if crate::leanh::lean_obj_tag(v___x_3568_) == 0 {
                    v___x_3569_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0);
                    v___y_3548_ = v___x_3569_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3570_ = crate::leanh::lean_ctor_get_uint64(
                        v___x_3568_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___x_3568_);
                    v___y_3548_ = v_hash_3570_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3549_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_snd_3545_);
                v___x_3550_ = lean_uint64_mix_hash(v___y_3548_, v___x_3549_);
                v___x_3551_ = 32u64;
                v___x_3552_ = lean_uint64_shift_right(v___x_3550_, v___x_3551_);
                v_fold_3553_ = lean_uint64_xor(v___x_3550_, v___x_3552_);
                v___x_3554_ = 16u64;
                v___x_3555_ = lean_uint64_shift_right(v_fold_3553_, v___x_3554_);
                v___x_3556_ = lean_uint64_xor(v_fold_3553_, v___x_3555_);
                v___x_3557_ = lean_uint64_to_usize(v___x_3556_);
                v___x_3558_ = lean_usize_of_nat(v___x_3546_);
                v___x_3559_ = 1usize;
                v___x_3560_ = lean_usize_sub(v___x_3558_, v___x_3559_);
                v___x_3561_ = lean_usize_land(v___x_3557_, v___x_3560_);
                v___x_3562_ = lean_array_uget_borrowed(v_x_3536_, v___x_3561_);
                crate::leanh::lean_inc(v___x_3562_);
                if v_isShared_3543_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3542_, 2, v___x_3562_);
                    v___x_3564_ = v___x_3542_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3567_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_key_3538_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 1, v_value_3539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 2, v___x_3562_);
                    v___x_3564_ = v_reuseFailAlloc_3567_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3565_ = lean_array_uset(v_x_3536_, v___x_3561_, v___x_3564_);
                v_x_3536_ = v___x_3565_;
                v_x_3537_ = v_tail_3540_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10___redArg(
    mut v_i_3572_: *mut crate::leanh::LeanObject,
    mut v_source_3573_: *mut crate::leanh::LeanObject,
    mut v_target_3574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: u8 = 0;
    let mut v_es_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3575_ = lean_array_get_size(v_source_3573_);
                v___x_3576_ = lean_nat_dec_lt(v_i_3572_, v___x_3575_);
                if v___x_3576_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3573_);
                    crate::leanh::lean_dec(v_i_3572_);
                    return v_target_3574_;
                } else {
                    v_es_3577_ = lean_array_fget(v_source_3573_, v_i_3572_);
                    v___x_3578_ = crate::leanh::lean_box(0);
                    v_source_3579_ = lean_array_fset(v_source_3573_, v_i_3572_, v___x_3578_);
                    v_target_3580_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg(v_target_3574_, v_es_3577_);
                    v___x_3581_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3582_ = lean_nat_add(v_i_3572_, v___x_3581_);
                    crate::leanh::lean_dec(v_i_3572_);
                    v_i_3572_ = v___x_3582_;
                    v_source_3573_ = v_source_3579_;
                    v_target_3574_ = v_target_3580_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8___redArg(
    mut v_data_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3585_ = lean_array_get_size(v_data_3584_);
    v___x_3586_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3587_ = lean_nat_mul(v___x_3585_, v___x_3586_);
    v___x_3588_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3589_ = crate::leanh::lean_box(0);
    v___x_3590_ = lean_mk_array(v_nbuckets_3587_, v___x_3589_);
    v___x_3591_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10___redArg(v___x_3588_, v_data_3584_, v___x_3590_);
    return v___x_3591_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4___redArg(
    mut v_m_3592_: *mut crate::leanh::LeanObject,
    mut v_a_3593_: *mut crate::leanh::LeanObject,
    mut v_b_3594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3601_: u64 = 0;
    let mut v___x_3602_: u64 = 0;
    let mut v___x_3603_: u64 = 0;
    let mut v___x_3604_: u64 = 0;
    let mut v___x_3605_: u64 = 0;
    let mut v_fold_3606_: u64 = 0;
    let mut v___x_3607_: u64 = 0;
    let mut v___x_3608_: u64 = 0;
    let mut v___x_3609_: u64 = 0;
    let mut v___x_3610_: usize = 0;
    let mut v___x_3611_: usize = 0;
    let mut v___x_3612_: usize = 0;
    let mut v___x_3613_: usize = 0;
    let mut v___x_3614_: usize = 0;
    let mut v_bkt_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: u8 = 0;
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3619_: u8 = 0;
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v_val_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3637_: u8 = 0;
    let mut v_unused_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u64 = 0;
    let mut v_hash_3642_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3595_ = crate::leanh::lean_ctor_get(v_m_3592_, 0);
                v_buckets_3596_ = crate::leanh::lean_ctor_get(v_m_3592_, 1);
                v_fst_3597_ = crate::leanh::lean_ctor_get(v_a_3593_, 0);
                v_snd_3598_ = crate::leanh::lean_ctor_get(v_a_3593_, 1);
                v___x_3599_ = lean_array_get_size(v_buckets_3596_);
                v___x_3640_ = l_Lean_Meta_Grind_Origin_key(v_fst_3597_);
                if crate::leanh::lean_obj_tag(v___x_3640_) == 0 {
                    v___x_3641_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0);
                    v___y_3601_ = v___x_3641_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3642_ = crate::leanh::lean_ctor_get_uint64(
                        v___x_3640_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___x_3640_);
                    v___y_3601_ = v_hash_3642_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3602_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_snd_3598_);
                v___x_3603_ = lean_uint64_mix_hash(v___y_3601_, v___x_3602_);
                v___x_3604_ = 32u64;
                v___x_3605_ = lean_uint64_shift_right(v___x_3603_, v___x_3604_);
                v_fold_3606_ = lean_uint64_xor(v___x_3603_, v___x_3605_);
                v___x_3607_ = 16u64;
                v___x_3608_ = lean_uint64_shift_right(v_fold_3606_, v___x_3607_);
                v___x_3609_ = lean_uint64_xor(v_fold_3606_, v___x_3608_);
                v___x_3610_ = lean_uint64_to_usize(v___x_3609_);
                v___x_3611_ = lean_usize_of_nat(v___x_3599_);
                v___x_3612_ = 1usize;
                v___x_3613_ = lean_usize_sub(v___x_3611_, v___x_3612_);
                v___x_3614_ = lean_usize_land(v___x_3610_, v___x_3613_);
                v_bkt_3615_ = lean_array_uget_borrowed(v_buckets_3596_, v___x_3614_);
                v___x_3616_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3_spec__6___redArg(v_a_3593_, v_bkt_3615_);
                if v___x_3616_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_3596_);
                    crate::leanh::lean_inc(v_size_3595_);
                    v_isSharedCheck_3637_ = (!crate::leanh::lean_is_exclusive(v_m_3592_)) as u8;
                    if v_isSharedCheck_3637_ == 0 {
                        v_unused_3638_ = crate::leanh::lean_ctor_get(v_m_3592_, 1);
                        crate::leanh::lean_dec(v_unused_3638_);
                        v_unused_3639_ = crate::leanh::lean_ctor_get(v_m_3592_, 0);
                        crate::leanh::lean_dec(v_unused_3639_);
                        v___x_3618_ = v_m_3592_;
                        v_isShared_3619_ = v_isSharedCheck_3637_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3592_);
                        v___x_3618_ = crate::leanh::lean_box(0);
                        v_isShared_3619_ = v_isSharedCheck_3637_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3594_);
                    crate::leanh::lean_dec_ref(v_a_3593_);
                    return v_m_3592_;
                }
            }
            2 => {
                v___x_3620_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3621_ = lean_nat_add(v_size_3595_, v___x_3620_);
                crate::leanh::lean_dec(v_size_3595_);
                crate::leanh::lean_inc(v_bkt_3615_);
                v___x_3622_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3622_, 0, v_a_3593_);
                crate::leanh::lean_ctor_set(v___x_3622_, 1, v_b_3594_);
                crate::leanh::lean_ctor_set(v___x_3622_, 2, v_bkt_3615_);
                v_buckets_x27_3623_ = lean_array_uset(v_buckets_3596_, v___x_3614_, v___x_3622_);
                v___x_3624_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3625_ = lean_nat_mul(v_size_x27_3621_, v___x_3624_);
                v___x_3626_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3627_ = lean_nat_div(v___x_3625_, v___x_3626_);
                crate::leanh::lean_dec(v___x_3625_);
                v___x_3628_ = lean_array_get_size(v_buckets_x27_3623_);
                v___x_3629_ = lean_nat_dec_le(v___x_3627_, v___x_3628_);
                crate::leanh::lean_dec(v___x_3627_);
                if v___x_3629_ == 0 {
                    v_val_3630_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8___redArg(v_buckets_x27_3623_);
                    if v_isShared_3619_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3618_, 1, v_val_3630_);
                        crate::leanh::lean_ctor_set(v___x_3618_, 0, v_size_x27_3621_);
                        v___x_3632_ = v___x_3618_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3633_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_size_x27_3621_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_val_3630_);
                        v___x_3632_ = v_reuseFailAlloc_3633_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_3619_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3618_, 1, v_buckets_x27_3623_);
                        crate::leanh::lean_ctor_set(v___x_3618_, 0, v_size_x27_3621_);
                        v___x_3635_ = v___x_3618_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3636_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_size_x27_3621_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_buckets_x27_3623_);
                        v___x_3635_ = v_reuseFailAlloc_3636_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3632_;
            }
            4 => {
                return v___x_3635_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0_spec__0___redArg(
    mut v_a_3643_: *mut crate::leanh::LeanObject,
    mut v_x_3644_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3645_: u8 = 0;
    let mut v_key_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3644_) == 0 {
                    v___x_3645_ = 0;
                    return v___x_3645_;
                } else {
                    v_key_3646_ = crate::leanh::lean_ctor_get(v_x_3644_, 0);
                    v_tail_3647_ = crate::leanh::lean_ctor_get(v_x_3644_, 2);
                    v___x_3648_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_3646_,
                            v_a_3643_,
                        );
                    if v___x_3648_ == 0 {
                        v_x_3644_ = v_tail_3647_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3648_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0_spec__0___redArg___boxed(
    mut v_a_3650_: *mut crate::leanh::LeanObject,
    mut v_x_3651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3652_: u8 = 0;
    let mut v_r_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0_spec__0___redArg(v_a_3650_, v_x_3651_);
    crate::leanh::lean_dec(v_x_3651_);
    crate::leanh::lean_dec_ref(v_a_3650_);
    v_r_3653_ = crate::leanh::lean_box((v_res_3652_) as usize);
    return v_r_3653_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0___redArg(
    mut v_m_3654_: *mut crate::leanh::LeanObject,
    mut v_a_3655_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: u64 = 0;
    let mut v___x_3659_: u64 = 0;
    let mut v___x_3660_: u64 = 0;
    let mut v_fold_3661_: u64 = 0;
    let mut v___x_3662_: u64 = 0;
    let mut v___x_3663_: u64 = 0;
    let mut v___x_3664_: u64 = 0;
    let mut v___x_3665_: usize = 0;
    let mut v___x_3666_: usize = 0;
    let mut v___x_3667_: usize = 0;
    let mut v___x_3668_: usize = 0;
    let mut v___x_3669_: usize = 0;
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: u8 = 0;
    v_buckets_3656_ = crate::leanh::lean_ctor_get(v_m_3654_, 1);
    v___x_3657_ = lean_array_get_size(v_buckets_3656_);
    v___x_3658_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_3655_);
    v___x_3659_ = 32u64;
    v___x_3660_ = lean_uint64_shift_right(v___x_3658_, v___x_3659_);
    v_fold_3661_ = lean_uint64_xor(v___x_3658_, v___x_3660_);
    v___x_3662_ = 16u64;
    v___x_3663_ = lean_uint64_shift_right(v_fold_3661_, v___x_3662_);
    v___x_3664_ = lean_uint64_xor(v_fold_3661_, v___x_3663_);
    v___x_3665_ = lean_uint64_to_usize(v___x_3664_);
    v___x_3666_ = lean_usize_of_nat(v___x_3657_);
    v___x_3667_ = 1usize;
    v___x_3668_ = lean_usize_sub(v___x_3666_, v___x_3667_);
    v___x_3669_ = lean_usize_land(v___x_3665_, v___x_3668_);
    v___x_3670_ = lean_array_uget_borrowed(v_buckets_3656_, v___x_3669_);
    v___x_3671_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0_spec__0___redArg(v_a_3655_, v___x_3670_);
    return v___x_3671_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0___redArg___boxed(
    mut v_m_3672_: *mut crate::leanh::LeanObject,
    mut v_a_3673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3674_: u8 = 0;
    let mut v_r_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3674_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0___redArg(v_m_3672_, v_a_3673_);
    crate::leanh::lean_dec_ref(v_a_3673_);
    crate::leanh::lean_dec_ref(v_m_3672_);
    v_r_3675_ = crate::leanh::lean_box((v_res_3674_) as usize);
    return v_r_3675_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2_spec__4___redArg(
    mut v_a_3676_: *mut crate::leanh::LeanObject,
    mut v_x_3677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: u8 = 0;
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3677_) == 0 {
                    v___x_3678_ = crate::leanh::lean_box(0);
                    return v___x_3678_;
                } else {
                    v_key_3679_ = crate::leanh::lean_ctor_get(v_x_3677_, 0);
                    v_value_3680_ = crate::leanh::lean_ctor_get(v_x_3677_, 1);
                    v_tail_3681_ = crate::leanh::lean_ctor_get(v_x_3677_, 2);
                    v___x_3682_ = lean_name_eq(v_key_3679_, v_a_3676_);
                    if v___x_3682_ == 0 {
                        v_x_3677_ = v_tail_3681_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3680_);
                        v___x_3684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3684_, 0, v_value_3680_);
                        return v___x_3684_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2_spec__4___redArg___boxed(
    mut v_a_3685_: *mut crate::leanh::LeanObject,
    mut v_x_3686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3687_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2_spec__4___redArg(v_a_3685_, v_x_3686_);
    crate::leanh::lean_dec(v_x_3686_);
    crate::leanh::lean_dec(v_a_3685_);
    return v_res_3687_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2___redArg(
    mut v_m_3688_: *mut crate::leanh::LeanObject,
    mut v_a_3689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3693_: u64 = 0;
    let mut v___x_3694_: u64 = 0;
    let mut v___x_3695_: u64 = 0;
    let mut v_fold_3696_: u64 = 0;
    let mut v___x_3697_: u64 = 0;
    let mut v___x_3698_: u64 = 0;
    let mut v___x_3699_: u64 = 0;
    let mut v___x_3700_: usize = 0;
    let mut v___x_3701_: usize = 0;
    let mut v___x_3702_: usize = 0;
    let mut v___x_3703_: usize = 0;
    let mut v___x_3704_: usize = 0;
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: u64 = 0;
    let mut v_hash_3708_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3690_ = crate::leanh::lean_ctor_get(v_m_3688_, 1);
                v___x_3691_ = lean_array_get_size(v_buckets_3690_);
                if crate::leanh::lean_obj_tag(v_a_3689_) == 0 {
                    v___x_3707_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0);
                    v___y_3693_ = v___x_3707_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3708_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_3689_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3693_ = v_hash_3708_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3694_ = 32u64;
                v___x_3695_ = lean_uint64_shift_right(v___y_3693_, v___x_3694_);
                v_fold_3696_ = lean_uint64_xor(v___y_3693_, v___x_3695_);
                v___x_3697_ = 16u64;
                v___x_3698_ = lean_uint64_shift_right(v_fold_3696_, v___x_3697_);
                v___x_3699_ = lean_uint64_xor(v_fold_3696_, v___x_3698_);
                v___x_3700_ = lean_uint64_to_usize(v___x_3699_);
                v___x_3701_ = lean_usize_of_nat(v___x_3691_);
                v___x_3702_ = 1usize;
                v___x_3703_ = lean_usize_sub(v___x_3701_, v___x_3702_);
                v___x_3704_ = lean_usize_land(v___x_3700_, v___x_3703_);
                v___x_3705_ = lean_array_uget_borrowed(v_buckets_3690_, v___x_3704_);
                v___x_3706_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2_spec__4___redArg(v_a_3689_, v___x_3705_);
                return v___x_3706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2___redArg___boxed(
    mut v_m_3709_: *mut crate::leanh::LeanObject,
    mut v_a_3710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3711_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2___redArg(v_m_3709_, v_a_3710_);
    crate::leanh::lean_dec(v_a_3710_);
    crate::leanh::lean_dec_ref(v_m_3709_);
    return v_res_3711_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2_spec__3_spec__7___redArg(
    mut v_x_3712_: *mut crate::leanh::LeanObject,
    mut v_x_3713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3719_: u8 = 0;
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: u64 = 0;
    let mut v___x_3722_: u64 = 0;
    let mut v___x_3723_: u64 = 0;
    let mut v_fold_3724_: u64 = 0;
    let mut v___x_3725_: u64 = 0;
    let mut v___x_3726_: u64 = 0;
    let mut v___x_3727_: u64 = 0;
    let mut v___x_3728_: usize = 0;
    let mut v___x_3729_: usize = 0;
    let mut v___x_3730_: usize = 0;
    let mut v___x_3731_: usize = 0;
    let mut v___x_3732_: usize = 0;
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3713_) == 0 {
                    return v_x_3712_;
                } else {
                    v_key_3714_ = crate::leanh::lean_ctor_get(v_x_3713_, 0);
                    v_value_3715_ = crate::leanh::lean_ctor_get(v_x_3713_, 1);
                    v_tail_3716_ = crate::leanh::lean_ctor_get(v_x_3713_, 2);
                    v_isSharedCheck_3739_ = (!crate::leanh::lean_is_exclusive(v_x_3713_)) as u8;
                    if v_isSharedCheck_3739_ == 0 {
                        v___x_3718_ = v_x_3713_;
                        v_isShared_3719_ = v_isSharedCheck_3739_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3716_);
                        crate::leanh::lean_inc(v_value_3715_);
                        crate::leanh::lean_inc(v_key_3714_);
                        crate::leanh::lean_dec(v_x_3713_);
                        v___x_3718_ = crate::leanh::lean_box(0);
                        v_isShared_3719_ = v_isSharedCheck_3739_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3720_ = lean_array_get_size(v_x_3712_);
                v___x_3721_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_3714_);
                v___x_3722_ = 32u64;
                v___x_3723_ = lean_uint64_shift_right(v___x_3721_, v___x_3722_);
                v_fold_3724_ = lean_uint64_xor(v___x_3721_, v___x_3723_);
                v___x_3725_ = 16u64;
                v___x_3726_ = lean_uint64_shift_right(v_fold_3724_, v___x_3725_);
                v___x_3727_ = lean_uint64_xor(v_fold_3724_, v___x_3726_);
                v___x_3728_ = lean_uint64_to_usize(v___x_3727_);
                v___x_3729_ = lean_usize_of_nat(v___x_3720_);
                v___x_3730_ = 1usize;
                v___x_3731_ = lean_usize_sub(v___x_3729_, v___x_3730_);
                v___x_3732_ = lean_usize_land(v___x_3728_, v___x_3731_);
                v___x_3733_ = lean_array_uget_borrowed(v_x_3712_, v___x_3732_);
                crate::leanh::lean_inc(v___x_3733_);
                if v_isShared_3719_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3718_, 2, v___x_3733_);
                    v___x_3735_ = v___x_3718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3738_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_key_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 1, v_value_3715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3738_, 2, v___x_3733_);
                    v___x_3735_ = v_reuseFailAlloc_3738_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3736_ = lean_array_uset(v_x_3712_, v___x_3732_, v___x_3735_);
                v_x_3712_ = v___x_3736_;
                v_x_3713_ = v_tail_3716_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2_spec__3___redArg(
    mut v_i_3740_: *mut crate::leanh::LeanObject,
    mut v_source_3741_: *mut crate::leanh::LeanObject,
    mut v_target_3742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: u8 = 0;
    let mut v_es_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3743_ = lean_array_get_size(v_source_3741_);
                v___x_3744_ = lean_nat_dec_lt(v_i_3740_, v___x_3743_);
                if v___x_3744_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3741_);
                    crate::leanh::lean_dec(v_i_3740_);
                    return v_target_3742_;
                } else {
                    v_es_3745_ = lean_array_fget(v_source_3741_, v_i_3740_);
                    v___x_3746_ = crate::leanh::lean_box(0);
                    v_source_3747_ = lean_array_fset(v_source_3741_, v_i_3740_, v___x_3746_);
                    v_target_3748_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2_spec__3_spec__7___redArg(v_target_3742_, v_es_3745_);
                    v___x_3749_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3750_ = lean_nat_add(v_i_3740_, v___x_3749_);
                    crate::leanh::lean_dec(v_i_3740_);
                    v_i_3740_ = v___x_3750_;
                    v_source_3741_ = v_source_3747_;
                    v_target_3742_ = v_target_3748_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2___redArg(
    mut v_data_3752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3753_ = lean_array_get_size(v_data_3752_);
    v___x_3754_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3755_ = lean_nat_mul(v___x_3753_, v___x_3754_);
    v___x_3756_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3757_ = crate::leanh::lean_box(0);
    v___x_3758_ = lean_mk_array(v_nbuckets_3755_, v___x_3757_);
    v___x_3759_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2_spec__3___redArg(v___x_3756_, v_data_3752_, v___x_3758_);
    return v___x_3759_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1___redArg(
    mut v_m_3760_: *mut crate::leanh::LeanObject,
    mut v_a_3761_: *mut crate::leanh::LeanObject,
    mut v_b_3762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: u64 = 0;
    let mut v___x_3767_: u64 = 0;
    let mut v___x_3768_: u64 = 0;
    let mut v_fold_3769_: u64 = 0;
    let mut v___x_3770_: u64 = 0;
    let mut v___x_3771_: u64 = 0;
    let mut v___x_3772_: u64 = 0;
    let mut v___x_3773_: usize = 0;
    let mut v___x_3774_: usize = 0;
    let mut v___x_3775_: usize = 0;
    let mut v___x_3776_: usize = 0;
    let mut v___x_3777_: usize = 0;
    let mut v_bkt_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: u8 = 0;
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3782_: u8 = 0;
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: u8 = 0;
    let mut v_val_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3800_: u8 = 0;
    let mut v_unused_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3763_ = crate::leanh::lean_ctor_get(v_m_3760_, 0);
                v_buckets_3764_ = crate::leanh::lean_ctor_get(v_m_3760_, 1);
                v___x_3765_ = lean_array_get_size(v_buckets_3764_);
                v___x_3766_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_3761_);
                v___x_3767_ = 32u64;
                v___x_3768_ = lean_uint64_shift_right(v___x_3766_, v___x_3767_);
                v_fold_3769_ = lean_uint64_xor(v___x_3766_, v___x_3768_);
                v___x_3770_ = 16u64;
                v___x_3771_ = lean_uint64_shift_right(v_fold_3769_, v___x_3770_);
                v___x_3772_ = lean_uint64_xor(v_fold_3769_, v___x_3771_);
                v___x_3773_ = lean_uint64_to_usize(v___x_3772_);
                v___x_3774_ = lean_usize_of_nat(v___x_3765_);
                v___x_3775_ = 1usize;
                v___x_3776_ = lean_usize_sub(v___x_3774_, v___x_3775_);
                v___x_3777_ = lean_usize_land(v___x_3773_, v___x_3776_);
                v_bkt_3778_ = lean_array_uget_borrowed(v_buckets_3764_, v___x_3777_);
                v___x_3779_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0_spec__0___redArg(v_a_3761_, v_bkt_3778_);
                if v___x_3779_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_3764_);
                    crate::leanh::lean_inc(v_size_3763_);
                    v_isSharedCheck_3800_ = (!crate::leanh::lean_is_exclusive(v_m_3760_)) as u8;
                    if v_isSharedCheck_3800_ == 0 {
                        v_unused_3801_ = crate::leanh::lean_ctor_get(v_m_3760_, 1);
                        crate::leanh::lean_dec(v_unused_3801_);
                        v_unused_3802_ = crate::leanh::lean_ctor_get(v_m_3760_, 0);
                        crate::leanh::lean_dec(v_unused_3802_);
                        v___x_3781_ = v_m_3760_;
                        v_isShared_3782_ = v_isSharedCheck_3800_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_3760_);
                        v___x_3781_ = crate::leanh::lean_box(0);
                        v_isShared_3782_ = v_isSharedCheck_3800_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_3762_);
                    crate::leanh::lean_dec_ref(v_a_3761_);
                    return v_m_3760_;
                }
            }
            1 => {
                v___x_3783_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_3784_ = lean_nat_add(v_size_3763_, v___x_3783_);
                crate::leanh::lean_dec(v_size_3763_);
                crate::leanh::lean_inc(v_bkt_3778_);
                v___x_3785_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3785_, 0, v_a_3761_);
                crate::leanh::lean_ctor_set(v___x_3785_, 1, v_b_3762_);
                crate::leanh::lean_ctor_set(v___x_3785_, 2, v_bkt_3778_);
                v_buckets_x27_3786_ = lean_array_uset(v_buckets_3764_, v___x_3777_, v___x_3785_);
                v___x_3787_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3788_ = lean_nat_mul(v_size_x27_3784_, v___x_3787_);
                v___x_3789_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3790_ = lean_nat_div(v___x_3788_, v___x_3789_);
                crate::leanh::lean_dec(v___x_3788_);
                v___x_3791_ = lean_array_get_size(v_buckets_x27_3786_);
                v___x_3792_ = lean_nat_dec_le(v___x_3790_, v___x_3791_);
                crate::leanh::lean_dec(v___x_3790_);
                if v___x_3792_ == 0 {
                    v_val_3793_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2___redArg(v_buckets_x27_3786_);
                    if v_isShared_3782_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3781_, 1, v_val_3793_);
                        crate::leanh::lean_ctor_set(v___x_3781_, 0, v_size_x27_3784_);
                        v___x_3795_ = v___x_3781_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3796_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_size_x27_3784_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3796_, 1, v_val_3793_);
                        v___x_3795_ = v_reuseFailAlloc_3796_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_3782_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3781_, 1, v_buckets_x27_3786_);
                        crate::leanh::lean_ctor_set(v___x_3781_, 0, v_size_x27_3784_);
                        v___x_3798_ = v___x_3781_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3799_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_size_x27_3784_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_buckets_x27_3786_);
                        v___x_3798_ = v_reuseFailAlloc_3799_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3795_;
            }
            3 => {
                return v___x_3798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3___redArg(
    mut v_m_3803_: *mut crate::leanh::LeanObject,
    mut v_a_3804_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3810_: u64 = 0;
    let mut v___x_3811_: u64 = 0;
    let mut v___x_3812_: u64 = 0;
    let mut v___x_3813_: u64 = 0;
    let mut v___x_3814_: u64 = 0;
    let mut v_fold_3815_: u64 = 0;
    let mut v___x_3816_: u64 = 0;
    let mut v___x_3817_: u64 = 0;
    let mut v___x_3818_: u64 = 0;
    let mut v___x_3819_: usize = 0;
    let mut v___x_3820_: usize = 0;
    let mut v___x_3821_: usize = 0;
    let mut v___x_3822_: usize = 0;
    let mut v___x_3823_: usize = 0;
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: u8 = 0;
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: u64 = 0;
    let mut v_hash_3828_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3805_ = crate::leanh::lean_ctor_get(v_m_3803_, 1);
                v_fst_3806_ = crate::leanh::lean_ctor_get(v_a_3804_, 0);
                v_snd_3807_ = crate::leanh::lean_ctor_get(v_a_3804_, 1);
                v___x_3808_ = lean_array_get_size(v_buckets_3805_);
                v___x_3826_ = l_Lean_Meta_Grind_Origin_key(v_fst_3806_);
                if crate::leanh::lean_obj_tag(v___x_3826_) == 0 {
                    v___x_3827_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0);
                    v___y_3810_ = v___x_3827_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3828_ = crate::leanh::lean_ctor_get_uint64(
                        v___x_3826_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___x_3826_);
                    v___y_3810_ = v_hash_3828_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3811_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_snd_3807_);
                v___x_3812_ = lean_uint64_mix_hash(v___y_3810_, v___x_3811_);
                v___x_3813_ = 32u64;
                v___x_3814_ = lean_uint64_shift_right(v___x_3812_, v___x_3813_);
                v_fold_3815_ = lean_uint64_xor(v___x_3812_, v___x_3814_);
                v___x_3816_ = 16u64;
                v___x_3817_ = lean_uint64_shift_right(v_fold_3815_, v___x_3816_);
                v___x_3818_ = lean_uint64_xor(v_fold_3815_, v___x_3817_);
                v___x_3819_ = lean_uint64_to_usize(v___x_3818_);
                v___x_3820_ = lean_usize_of_nat(v___x_3808_);
                v___x_3821_ = 1usize;
                v___x_3822_ = lean_usize_sub(v___x_3820_, v___x_3821_);
                v___x_3823_ = lean_usize_land(v___x_3819_, v___x_3822_);
                v___x_3824_ = lean_array_uget_borrowed(v_buckets_3805_, v___x_3823_);
                v___x_3825_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3_spec__6___redArg(v_a_3804_, v___x_3824_);
                return v___x_3825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3___redArg___boxed(
    mut v_m_3829_: *mut crate::leanh::LeanObject,
    mut v_a_3830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3831_: u8 = 0;
    let mut v_r_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3831_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3___redArg(v_m_3829_, v_a_3830_);
    crate::leanh::lean_dec_ref(v_a_3830_);
    crate::leanh::lean_dec_ref(v_m_3829_);
    v_r_3832_ = crate::leanh::lean_box((v_res_3831_) as usize);
    return v_r_3832_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go(
    mut v_map_3833_: *mut crate::leanh::LeanObject,
    mut v_e_3834_: *mut crate::leanh::LeanObject,
    mut v_a_3835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: u8 = 0;
    let mut v_visited_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_collectedThms_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thms_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: u8 = 0;
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3875_: u8 = 0;
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: u8 = 0;
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3892_: u8 = 0;
    let mut v_unused_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3868_ = l_Lean_Meta_Grind_isMarkedSubsingletonApp(v_e_3834_);
                if v___x_3868_ == 0 {
                    v_visited_3869_ = crate::leanh::lean_ctor_get(v_a_3835_, 0);
                    v_collectedThms_3870_ = crate::leanh::lean_ctor_get(v_a_3835_, 1);
                    v_thms_3871_ = crate::leanh::lean_ctor_get(v_a_3835_, 2);
                    v___x_3872_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0___redArg(v_visited_3869_, v_e_3834_);
                    if v___x_3872_ == 0 {
                        crate::leanh::lean_inc_ref(v_thms_3871_);
                        crate::leanh::lean_inc_ref(v_collectedThms_3870_);
                        crate::leanh::lean_inc_ref(v_visited_3869_);
                        v_isSharedCheck_3892_ = (!crate::leanh::lean_is_exclusive(v_a_3835_)) as u8;
                        if v_isSharedCheck_3892_ == 0 {
                            v_unused_3893_ = crate::leanh::lean_ctor_get(v_a_3835_, 2);
                            crate::leanh::lean_dec(v_unused_3893_);
                            v_unused_3894_ = crate::leanh::lean_ctor_get(v_a_3835_, 1);
                            crate::leanh::lean_dec(v_unused_3894_);
                            v_unused_3895_ = crate::leanh::lean_ctor_get(v_a_3835_, 0);
                            crate::leanh::lean_dec(v_unused_3895_);
                            v___x_3874_ = v_a_3835_;
                            v_isShared_3875_ = v_isSharedCheck_3892_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3835_);
                            v___x_3874_ = crate::leanh::lean_box(0);
                            v_isShared_3875_ = v_isSharedCheck_3892_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3834_);
                        v___x_3896_ = crate::leanh::lean_box(0);
                        v___x_3897_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3897_, 0, v___x_3896_);
                        crate::leanh::lean_ctor_set(v___x_3897_, 1, v_a_3835_);
                        return v___x_3897_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3834_);
                    v___x_3898_ = crate::leanh::lean_box(0);
                    v___x_3899_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3899_, 0, v___x_3898_);
                    crate::leanh::lean_ctor_set(v___x_3899_, 1, v_a_3835_);
                    return v___x_3899_;
                }
            }
            1 => {
                v___x_3840_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go(v_map_3833_, v_d_3837_, v___y_3839_);
                v_snd_3841_ = crate::leanh::lean_ctor_get(v___x_3840_, 1);
                crate::leanh::lean_inc(v_snd_3841_);
                crate::leanh::lean_dec_ref(v___x_3840_);
                v_e_3834_ = v_b_3838_;
                v_a_3835_ = v_snd_3841_;
                state = 0;
                continue;
            }
            2 => match crate::leanh::lean_obj_tag(v_e_3834_) {
                6 => {
                    v_binderType_3845_ = crate::leanh::lean_ctor_get(v_e_3834_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_3845_);
                    v_body_3846_ = crate::leanh::lean_ctor_get(v_e_3834_, 2);
                    crate::leanh::lean_inc_ref(v_body_3846_);
                    crate::leanh::lean_dec_ref_known(v_e_3834_, 3);
                    v_d_3837_ = v_binderType_3845_;
                    v_b_3838_ = v_body_3846_;
                    v___y_3839_ = v___y_3844_;
                    state = 1;
                    continue;
                }
                7 => {
                    v_binderType_3847_ = crate::leanh::lean_ctor_get(v_e_3834_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_3847_);
                    v_body_3848_ = crate::leanh::lean_ctor_get(v_e_3834_, 2);
                    crate::leanh::lean_inc_ref(v_body_3848_);
                    crate::leanh::lean_dec_ref_known(v_e_3834_, 3);
                    v_d_3837_ = v_binderType_3847_;
                    v_b_3838_ = v_body_3848_;
                    v___y_3839_ = v___y_3844_;
                    state = 1;
                    continue;
                }
                11 => {
                    v_struct_3849_ = crate::leanh::lean_ctor_get(v_e_3834_, 2);
                    crate::leanh::lean_inc_ref(v_struct_3849_);
                    crate::leanh::lean_dec_ref_known(v_e_3834_, 3);
                    v_e_3834_ = v_struct_3849_;
                    v_a_3835_ = v___y_3844_;
                    state = 0;
                    continue;
                }
                10 => {
                    v_expr_3851_ = crate::leanh::lean_ctor_get(v_e_3834_, 1);
                    crate::leanh::lean_inc_ref(v_expr_3851_);
                    crate::leanh::lean_dec_ref_known(v_e_3834_, 2);
                    v_e_3834_ = v_expr_3851_;
                    v_a_3835_ = v___y_3844_;
                    state = 0;
                    continue;
                }
                8 => {
                    v_type_3853_ = crate::leanh::lean_ctor_get(v_e_3834_, 1);
                    crate::leanh::lean_inc_ref(v_type_3853_);
                    v_value_3854_ = crate::leanh::lean_ctor_get(v_e_3834_, 2);
                    crate::leanh::lean_inc_ref(v_value_3854_);
                    v_body_3855_ = crate::leanh::lean_ctor_get(v_e_3834_, 3);
                    crate::leanh::lean_inc_ref(v_body_3855_);
                    crate::leanh::lean_dec_ref_known(v_e_3834_, 4);
                    v___x_3856_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go(v_map_3833_, v_type_3853_, v___y_3844_);
                    v_snd_3857_ = crate::leanh::lean_ctor_get(v___x_3856_, 1);
                    crate::leanh::lean_inc(v_snd_3857_);
                    crate::leanh::lean_dec_ref(v___x_3856_);
                    v___x_3858_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go(v_map_3833_, v_value_3854_, v_snd_3857_);
                    v_snd_3859_ = crate::leanh::lean_ctor_get(v___x_3858_, 1);
                    crate::leanh::lean_inc(v_snd_3859_);
                    crate::leanh::lean_dec_ref(v___x_3858_);
                    v_e_3834_ = v_body_3855_;
                    v_a_3835_ = v_snd_3859_;
                    state = 0;
                    continue;
                }
                5 => {
                    v_fn_3861_ = crate::leanh::lean_ctor_get(v_e_3834_, 0);
                    crate::leanh::lean_inc_ref(v_fn_3861_);
                    v_arg_3862_ = crate::leanh::lean_ctor_get(v_e_3834_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3862_);
                    crate::leanh::lean_dec_ref_known(v_e_3834_, 2);
                    v___x_3863_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go(v_map_3833_, v_fn_3861_, v___y_3844_);
                    v_snd_3864_ = crate::leanh::lean_ctor_get(v___x_3863_, 1);
                    crate::leanh::lean_inc(v_snd_3864_);
                    crate::leanh::lean_dec_ref(v___x_3863_);
                    v_e_3834_ = v_arg_3862_;
                    v_a_3835_ = v_snd_3864_;
                    state = 0;
                    continue;
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_e_3834_);
                    v___x_3866_ = crate::leanh::lean_box(0);
                    v___x_3867_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3867_, 0, v___x_3866_);
                    crate::leanh::lean_ctor_set(v___x_3867_, 1, v___y_3844_);
                    return v___x_3867_;
                }
            },
            3 => {
                v___x_3876_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v_e_3834_);
                v___x_3877_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1___redArg(v_visited_3869_, v_e_3834_, v___x_3876_);
                crate::leanh::lean_inc_ref(v_thms_3871_);
                crate::leanh::lean_inc_ref(v_collectedThms_3870_);
                crate::leanh::lean_inc_ref(v___x_3877_);
                if v_isShared_3875_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3874_, 0, v___x_3877_);
                    v___x_3879_ = v___x_3874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3891_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_collectedThms_3870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_thms_3871_);
                    v___x_3879_ = v_reuseFailAlloc_3891_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3880_ = l_Lean_Meta_Grind_EMatch_isTheoremInstanceProof_x3f(v_e_3834_);
                if crate::leanh::lean_obj_tag(v___x_3880_) == 1 {
                    v_val_3881_ = crate::leanh::lean_ctor_get(v___x_3880_, 0);
                    crate::leanh::lean_inc(v_val_3881_);
                    crate::leanh::lean_dec_ref_known(v___x_3880_, 1);
                    v___x_3882_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2___redArg(v_map_3833_, v_val_3881_);
                    crate::leanh::lean_dec(v_val_3881_);
                    if crate::leanh::lean_obj_tag(v___x_3882_) == 1 {
                        v_val_3883_ = crate::leanh::lean_ctor_get(v___x_3882_, 0);
                        crate::leanh::lean_inc(v_val_3883_);
                        crate::leanh::lean_dec_ref_known(v___x_3882_, 1);
                        v_origin_3884_ = crate::leanh::lean_ctor_get(v_val_3883_, 5);
                        v_kind_3885_ = crate::leanh::lean_ctor_get(v_val_3883_, 6);
                        crate::leanh::lean_inc(v_kind_3885_);
                        crate::leanh::lean_inc_ref(v_origin_3884_);
                        v___x_3886_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3886_, 0, v_origin_3884_);
                        crate::leanh::lean_ctor_set(v___x_3886_, 1, v_kind_3885_);
                        v___x_3887_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3___redArg(v_collectedThms_3870_, v___x_3886_);
                        if v___x_3887_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3879_);
                            v___x_3888_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4___redArg(v_collectedThms_3870_, v___x_3886_, v___x_3876_);
                            v___x_3889_ = lean_array_push(v_thms_3871_, v_val_3883_);
                            v___x_3890_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3890_, 0, v___x_3877_);
                            crate::leanh::lean_ctor_set(v___x_3890_, 1, v___x_3888_);
                            crate::leanh::lean_ctor_set(v___x_3890_, 2, v___x_3889_);
                            v___y_3844_ = v___x_3890_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_3886_, 2);
                            crate::leanh::lean_dec(v_val_3883_);
                            crate::leanh::lean_dec_ref(v___x_3877_);
                            crate::leanh::lean_dec_ref(v_thms_3871_);
                            crate::leanh::lean_dec_ref(v_collectedThms_3870_);
                            v___y_3844_ = v___x_3879_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3882_);
                        crate::leanh::lean_dec_ref(v___x_3877_);
                        crate::leanh::lean_dec_ref(v_thms_3871_);
                        crate::leanh::lean_dec_ref(v_collectedThms_3870_);
                        v___y_3844_ = v___x_3879_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3880_);
                    crate::leanh::lean_dec_ref(v___x_3877_);
                    crate::leanh::lean_dec_ref(v_thms_3871_);
                    crate::leanh::lean_dec_ref(v_collectedThms_3870_);
                    v___y_3844_ = v___x_3879_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go___boxed(
    mut v_map_3900_: *mut crate::leanh::LeanObject,
    mut v_e_3901_: *mut crate::leanh::LeanObject,
    mut v_a_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3903_ =
        l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go(
            v_map_3900_,
            v_e_3901_,
            v_a_3902_,
        );
    crate::leanh::lean_dec_ref(v_map_3900_);
    return v_res_3903_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0(
    mut v_00_u03b2_3904_: *mut crate::leanh::LeanObject,
    mut v_m_3905_: *mut crate::leanh::LeanObject,
    mut v_a_3906_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3907_: u8 = 0;
    v___x_3907_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0___redArg(v_m_3905_, v_a_3906_);
    return v___x_3907_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0___boxed(
    mut v_00_u03b2_3908_: *mut crate::leanh::LeanObject,
    mut v_m_3909_: *mut crate::leanh::LeanObject,
    mut v_a_3910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3911_: u8 = 0;
    let mut v_r_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3911_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0(v_00_u03b2_3908_, v_m_3909_, v_a_3910_);
    crate::leanh::lean_dec_ref(v_a_3910_);
    crate::leanh::lean_dec_ref(v_m_3909_);
    v_r_3912_ = crate::leanh::lean_box((v_res_3911_) as usize);
    return v_r_3912_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1(
    mut v_00_u03b2_3913_: *mut crate::leanh::LeanObject,
    mut v_m_3914_: *mut crate::leanh::LeanObject,
    mut v_a_3915_: *mut crate::leanh::LeanObject,
    mut v_b_3916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3917_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1___redArg(v_m_3914_, v_a_3915_, v_b_3916_);
    return v___x_3917_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2(
    mut v_00_u03b2_3918_: *mut crate::leanh::LeanObject,
    mut v_m_3919_: *mut crate::leanh::LeanObject,
    mut v_a_3920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3921_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2___redArg(v_m_3919_, v_a_3920_);
    return v___x_3921_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2___boxed(
    mut v_00_u03b2_3922_: *mut crate::leanh::LeanObject,
    mut v_m_3923_: *mut crate::leanh::LeanObject,
    mut v_a_3924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3925_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2(v_00_u03b2_3922_, v_m_3923_, v_a_3924_);
    crate::leanh::lean_dec(v_a_3924_);
    crate::leanh::lean_dec_ref(v_m_3923_);
    return v_res_3925_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3(
    mut v_00_u03b2_3926_: *mut crate::leanh::LeanObject,
    mut v_m_3927_: *mut crate::leanh::LeanObject,
    mut v_a_3928_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3929_: u8 = 0;
    v___x_3929_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3___redArg(v_m_3927_, v_a_3928_);
    return v___x_3929_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3___boxed(
    mut v_00_u03b2_3930_: *mut crate::leanh::LeanObject,
    mut v_m_3931_: *mut crate::leanh::LeanObject,
    mut v_a_3932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3933_: u8 = 0;
    let mut v_r_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3933_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3(v_00_u03b2_3930_, v_m_3931_, v_a_3932_);
    crate::leanh::lean_dec_ref(v_a_3932_);
    crate::leanh::lean_dec_ref(v_m_3931_);
    v_r_3934_ = crate::leanh::lean_box((v_res_3933_) as usize);
    return v_r_3934_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4(
    mut v_00_u03b2_3935_: *mut crate::leanh::LeanObject,
    mut v_m_3936_: *mut crate::leanh::LeanObject,
    mut v_a_3937_: *mut crate::leanh::LeanObject,
    mut v_b_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4___redArg(v_m_3936_, v_a_3937_, v_b_3938_);
    return v___x_3939_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0_spec__0(
    mut v_00_u03b2_3940_: *mut crate::leanh::LeanObject,
    mut v_a_3941_: *mut crate::leanh::LeanObject,
    mut v_x_3942_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3943_: u8 = 0;
    v___x_3943_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0_spec__0___redArg(v_a_3941_, v_x_3942_);
    return v___x_3943_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_3944_: *mut crate::leanh::LeanObject,
    mut v_a_3945_: *mut crate::leanh::LeanObject,
    mut v_x_3946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3947_: u8 = 0;
    let mut v_r_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3947_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__0_spec__0(v_00_u03b2_3944_, v_a_3945_, v_x_3946_);
    crate::leanh::lean_dec(v_x_3946_);
    crate::leanh::lean_dec_ref(v_a_3945_);
    v_r_3948_ = crate::leanh::lean_box((v_res_3947_) as usize);
    return v_r_3948_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2(
    mut v_00_u03b2_3949_: *mut crate::leanh::LeanObject,
    mut v_data_3950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3951_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2___redArg(v_data_3950_);
    return v___x_3951_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2_spec__4(
    mut v_00_u03b2_3952_: *mut crate::leanh::LeanObject,
    mut v_a_3953_: *mut crate::leanh::LeanObject,
    mut v_x_3954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3955_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2_spec__4___redArg(v_a_3953_, v_x_3954_);
    return v___x_3955_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2_spec__4___boxed(
    mut v_00_u03b2_3956_: *mut crate::leanh::LeanObject,
    mut v_a_3957_: *mut crate::leanh::LeanObject,
    mut v_x_3958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3959_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__2_spec__4(v_00_u03b2_3956_, v_a_3957_, v_x_3958_);
    crate::leanh::lean_dec(v_x_3958_);
    crate::leanh::lean_dec(v_a_3957_);
    return v_res_3959_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3_spec__6(
    mut v_00_u03b2_3960_: *mut crate::leanh::LeanObject,
    mut v_a_3961_: *mut crate::leanh::LeanObject,
    mut v_x_3962_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3963_: u8 = 0;
    v___x_3963_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3_spec__6___redArg(v_a_3961_, v_x_3962_);
    return v___x_3963_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3_spec__6___boxed(
    mut v_00_u03b2_3964_: *mut crate::leanh::LeanObject,
    mut v_a_3965_: *mut crate::leanh::LeanObject,
    mut v_x_3966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3967_: u8 = 0;
    let mut v_r_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3967_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__3_spec__6(v_00_u03b2_3964_, v_a_3965_, v_x_3966_);
    crate::leanh::lean_dec(v_x_3966_);
    crate::leanh::lean_dec_ref(v_a_3965_);
    v_r_3968_ = crate::leanh::lean_box((v_res_3967_) as usize);
    return v_r_3968_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8(
    mut v_00_u03b2_3969_: *mut crate::leanh::LeanObject,
    mut v_data_3970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3971_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8___redArg(v_data_3970_);
    return v___x_3971_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3972_: *mut crate::leanh::LeanObject,
    mut v_i_3973_: *mut crate::leanh::LeanObject,
    mut v_source_3974_: *mut crate::leanh::LeanObject,
    mut v_target_3975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3976_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2_spec__3___redArg(v_i_3973_, v_source_3974_, v_target_3975_);
    return v___x_3976_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10(
    mut v_00_u03b2_3977_: *mut crate::leanh::LeanObject,
    mut v_i_3978_: *mut crate::leanh::LeanObject,
    mut v_source_3979_: *mut crate::leanh::LeanObject,
    mut v_target_3980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3981_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10___redArg(v_i_3978_, v_source_3979_, v_target_3980_);
    return v___x_3981_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2_spec__3_spec__7(
    mut v_00_u03b2_3982_: *mut crate::leanh::LeanObject,
    mut v_x_3983_: *mut crate::leanh::LeanObject,
    mut v_x_3984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3985_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__1_spec__2_spec__3_spec__7___redArg(v_x_3983_, v_x_3984_);
    return v___x_3985_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12(
    mut v_00_u03b2_3986_: *mut crate::leanh::LeanObject,
    mut v_x_3987_: *mut crate::leanh::LeanObject,
    mut v_x_3988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3989_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg(v_x_3987_, v_x_3988_);
    return v___x_3989_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3990_ = crate::leanh::lean_box(0);
    v___x_3991_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3992_ = lean_mk_array(v___x_3991_, v___x_3990_);
    return v___x_3992_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3993_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__0);
    v___x_3994_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3995_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3995_, 0, v___x_3994_);
    crate::leanh::lean_ctor_set(v___x_3995_, 1, v___x_3993_);
    return v___x_3995_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3998_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__2;
    v___x_3999_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__1);
    v___x_4000_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4000_, 0, v___x_3999_);
    crate::leanh::lean_ctor_set(v___x_4000_, 1, v___x_3999_);
    crate::leanh::lean_ctor_set(v___x_4000_, 2, v___x_3998_);
    return v___x_4000_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect(
    mut v_e_4001_: *mut crate::leanh::LeanObject,
    mut v_map_4002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thms_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4003_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__3);
    v___x_4004_ =
        l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go(
            v_map_4002_,
            v_e_4001_,
            v___x_4003_,
        );
    v_snd_4005_ = crate::leanh::lean_ctor_get(v___x_4004_, 1);
    crate::leanh::lean_inc(v_snd_4005_);
    crate::leanh::lean_dec_ref(v___x_4004_);
    v_thms_4006_ = crate::leanh::lean_ctor_get(v_snd_4005_, 2);
    crate::leanh::lean_inc_ref(v_thms_4006_);
    crate::leanh::lean_dec(v_snd_4005_);
    return v_thms_4006_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___boxed(
    mut v_e_4007_: *mut crate::leanh::LeanObject,
    mut v_map_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4009_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect(
        v_e_4007_,
        v_map_4008_,
    );
    crate::leanh::lean_dec_ref(v_map_4008_);
    return v_res_4009_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___redArg___lam__0(
    mut v_x_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
    mut v___y_4015_: *mut crate::leanh::LeanObject,
    mut v___y_4016_: *mut crate::leanh::LeanObject,
    mut v___y_4017_: *mut crate::leanh::LeanObject,
    mut v___y_4018_: *mut crate::leanh::LeanObject,
    mut v___y_4019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4015_);
    crate::leanh::lean_inc_ref(v___y_4014_);
    crate::leanh::lean_inc(v___y_4013_);
    crate::leanh::lean_inc_ref(v___y_4012_);
    crate::leanh::lean_inc(v___y_4011_);
    v___x_4021_ = crate::leanh::lean_apply_10(
        v_x_4010_,
        v___y_4011_,
        v___y_4012_,
        v___y_4013_,
        v___y_4014_,
        v___y_4015_,
        v___y_4016_,
        v___y_4017_,
        v___y_4018_,
        v___y_4019_,
        crate::leanh::lean_box(0),
    );
    return v___x_4021_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___redArg___lam__0___boxed(
    mut v_x_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
    mut v___y_4027_: *mut crate::leanh::LeanObject,
    mut v___y_4028_: *mut crate::leanh::LeanObject,
    mut v___y_4029_: *mut crate::leanh::LeanObject,
    mut v___y_4030_: *mut crate::leanh::LeanObject,
    mut v___y_4031_: *mut crate::leanh::LeanObject,
    mut v___y_4032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4033_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___redArg___lam__0(v_x_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
    crate::leanh::lean_dec(v___y_4027_);
    crate::leanh::lean_dec_ref(v___y_4026_);
    crate::leanh::lean_dec(v___y_4025_);
    crate::leanh::lean_dec_ref(v___y_4024_);
    crate::leanh::lean_dec(v___y_4023_);
    return v_res_4033_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___redArg(
    mut v_mvarId_4034_: *mut crate::leanh::LeanObject,
    mut v_x_4035_: *mut crate::leanh::LeanObject,
    mut v___y_4036_: *mut crate::leanh::LeanObject,
    mut v___y_4037_: *mut crate::leanh::LeanObject,
    mut v___y_4038_: *mut crate::leanh::LeanObject,
    mut v___y_4039_: *mut crate::leanh::LeanObject,
    mut v___y_4040_: *mut crate::leanh::LeanObject,
    mut v___y_4041_: *mut crate::leanh::LeanObject,
    mut v___y_4042_: *mut crate::leanh::LeanObject,
    mut v___y_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4051_: u8 = 0;
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4040_);
                crate::leanh::lean_inc_ref(v___y_4039_);
                crate::leanh::lean_inc(v___y_4038_);
                crate::leanh::lean_inc_ref(v___y_4037_);
                crate::leanh::lean_inc(v___y_4036_);
                v___f_4046_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                crate::leanh::lean_closure_set(v___f_4046_, 0, v_x_4035_);
                crate::leanh::lean_closure_set(v___f_4046_, 1, v___y_4036_);
                crate::leanh::lean_closure_set(v___f_4046_, 2, v___y_4037_);
                crate::leanh::lean_closure_set(v___f_4046_, 3, v___y_4038_);
                crate::leanh::lean_closure_set(v___f_4046_, 4, v___y_4039_);
                crate::leanh::lean_closure_set(v___f_4046_, 5, v___y_4040_);
                v___x_4047_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_4034_,
                    v___f_4046_,
                    v___y_4041_,
                    v___y_4042_,
                    v___y_4043_,
                    v___y_4044_,
                );
                if crate::leanh::lean_obj_tag(v___x_4047_) == 0 {
                    return v___x_4047_;
                } else {
                    v_a_4048_ = crate::leanh::lean_ctor_get(v___x_4047_, 0);
                    v_isSharedCheck_4055_ = (!crate::leanh::lean_is_exclusive(v___x_4047_)) as u8;
                    if v_isSharedCheck_4055_ == 0 {
                        v___x_4050_ = v___x_4047_;
                        v_isShared_4051_ = v_isSharedCheck_4055_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4048_);
                        crate::leanh::lean_dec(v___x_4047_);
                        v___x_4050_ = crate::leanh::lean_box(0);
                        v_isShared_4051_ = v_isSharedCheck_4055_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4051_ == 0 {
                    v___x_4053_ = v___x_4050_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
                    v___x_4053_ = v_reuseFailAlloc_4054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___redArg___boxed(
    mut v_mvarId_4056_: *mut crate::leanh::LeanObject,
    mut v_x_4057_: *mut crate::leanh::LeanObject,
    mut v___y_4058_: *mut crate::leanh::LeanObject,
    mut v___y_4059_: *mut crate::leanh::LeanObject,
    mut v___y_4060_: *mut crate::leanh::LeanObject,
    mut v___y_4061_: *mut crate::leanh::LeanObject,
    mut v___y_4062_: *mut crate::leanh::LeanObject,
    mut v___y_4063_: *mut crate::leanh::LeanObject,
    mut v___y_4064_: *mut crate::leanh::LeanObject,
    mut v___y_4065_: *mut crate::leanh::LeanObject,
    mut v___y_4066_: *mut crate::leanh::LeanObject,
    mut v___y_4067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4068_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___redArg(v_mvarId_4056_, v_x_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
    crate::leanh::lean_dec(v___y_4066_);
    crate::leanh::lean_dec_ref(v___y_4065_);
    crate::leanh::lean_dec(v___y_4064_);
    crate::leanh::lean_dec_ref(v___y_4063_);
    crate::leanh::lean_dec(v___y_4062_);
    crate::leanh::lean_dec_ref(v___y_4061_);
    crate::leanh::lean_dec(v___y_4060_);
    crate::leanh::lean_dec_ref(v___y_4059_);
    crate::leanh::lean_dec(v___y_4058_);
    return v_res_4068_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3(
    mut v_00_u03b1_4069_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4070_: *mut crate::leanh::LeanObject,
    mut v_x_4071_: *mut crate::leanh::LeanObject,
    mut v___y_4072_: *mut crate::leanh::LeanObject,
    mut v___y_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
    mut v___y_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
    mut v___y_4080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4082_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___redArg(v_mvarId_4070_, v_x_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
    return v___x_4082_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___boxed(
    mut v_00_u03b1_4083_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4084_: *mut crate::leanh::LeanObject,
    mut v_x_4085_: *mut crate::leanh::LeanObject,
    mut v___y_4086_: *mut crate::leanh::LeanObject,
    mut v___y_4087_: *mut crate::leanh::LeanObject,
    mut v___y_4088_: *mut crate::leanh::LeanObject,
    mut v___y_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4096_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3(v_00_u03b1_4083_, v_mvarId_4084_, v_x_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
    crate::leanh::lean_dec(v___y_4094_);
    crate::leanh::lean_dec_ref(v___y_4093_);
    crate::leanh::lean_dec(v___y_4092_);
    crate::leanh::lean_dec_ref(v___y_4091_);
    crate::leanh::lean_dec(v___y_4090_);
    crate::leanh::lean_dec_ref(v___y_4089_);
    crate::leanh::lean_dec(v___y_4088_);
    crate::leanh::lean_dec_ref(v___y_4087_);
    crate::leanh::lean_dec(v___y_4086_);
    return v_res_4096_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0_spec__0___redArg(
    mut v_a_4097_: *mut crate::leanh::LeanObject,
    mut v_x_4098_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4099_: u8 = 0;
    let mut v_key_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4098_) == 0 {
                    v___x_4099_ = 0;
                    return v___x_4099_;
                } else {
                    v_key_4100_ = crate::leanh::lean_ctor_get(v_x_4098_, 0);
                    v_tail_4101_ = crate::leanh::lean_ctor_get(v_x_4098_, 2);
                    v___x_4102_ = l_Lean_Meta_Grind_Origin_key(v_key_4100_);
                    v___x_4103_ = l_Lean_Meta_Grind_Origin_key(v_a_4097_);
                    v___x_4104_ = lean_name_eq(v___x_4102_, v___x_4103_);
                    crate::leanh::lean_dec(v___x_4103_);
                    crate::leanh::lean_dec(v___x_4102_);
                    if v___x_4104_ == 0 {
                        v_x_4098_ = v_tail_4101_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4104_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0_spec__0___redArg___boxed(
    mut v_a_4106_: *mut crate::leanh::LeanObject,
    mut v_x_4107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4108_: u8 = 0;
    let mut v_r_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0_spec__0___redArg(v_a_4106_, v_x_4107_);
    crate::leanh::lean_dec(v_x_4107_);
    crate::leanh::lean_dec_ref(v_a_4106_);
    v_r_4109_ = crate::leanh::lean_box((v_res_4108_) as usize);
    return v_r_4109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0___redArg(
    mut v_m_4110_: *mut crate::leanh::LeanObject,
    mut v_a_4111_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: u64 = 0;
    let mut v___x_4116_: u64 = 0;
    let mut v___x_4117_: u64 = 0;
    let mut v_fold_4118_: u64 = 0;
    let mut v___x_4119_: u64 = 0;
    let mut v___x_4120_: u64 = 0;
    let mut v___x_4121_: u64 = 0;
    let mut v___x_4122_: usize = 0;
    let mut v___x_4123_: usize = 0;
    let mut v___x_4124_: usize = 0;
    let mut v___x_4125_: usize = 0;
    let mut v___x_4126_: usize = 0;
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: u8 = 0;
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: u64 = 0;
    let mut v_hash_4131_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4112_ = crate::leanh::lean_ctor_get(v_m_4110_, 1);
                v___x_4113_ = lean_array_get_size(v_buckets_4112_);
                v___x_4129_ = l_Lean_Meta_Grind_Origin_key(v_a_4111_);
                if crate::leanh::lean_obj_tag(v___x_4129_) == 0 {
                    v___x_4130_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0);
                    v___y_4115_ = v___x_4130_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4131_ = crate::leanh::lean_ctor_get_uint64(
                        v___x_4129_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___x_4129_);
                    v___y_4115_ = v_hash_4131_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4116_ = 32u64;
                v___x_4117_ = lean_uint64_shift_right(v___y_4115_, v___x_4116_);
                v_fold_4118_ = lean_uint64_xor(v___y_4115_, v___x_4117_);
                v___x_4119_ = 16u64;
                v___x_4120_ = lean_uint64_shift_right(v_fold_4118_, v___x_4119_);
                v___x_4121_ = lean_uint64_xor(v_fold_4118_, v___x_4120_);
                v___x_4122_ = lean_uint64_to_usize(v___x_4121_);
                v___x_4123_ = lean_usize_of_nat(v___x_4113_);
                v___x_4124_ = 1usize;
                v___x_4125_ = lean_usize_sub(v___x_4123_, v___x_4124_);
                v___x_4126_ = lean_usize_land(v___x_4122_, v___x_4125_);
                v___x_4127_ = lean_array_uget_borrowed(v_buckets_4112_, v___x_4126_);
                v___x_4128_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0_spec__0___redArg(v_a_4111_, v___x_4127_);
                return v___x_4128_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0___redArg___boxed(
    mut v_m_4132_: *mut crate::leanh::LeanObject,
    mut v_a_4133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4134_: u8 = 0;
    let mut v_r_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4134_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0___redArg(v_m_4132_, v_a_4133_);
    crate::leanh::lean_dec_ref(v_a_4133_);
    crate::leanh::lean_dec_ref(v_m_4132_);
    v_r_4135_ = crate::leanh::lean_box((v_res_4134_) as usize);
    return v_r_4135_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_x_4136_: *mut crate::leanh::LeanObject,
    mut v_x_4137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4143_: u8 = 0;
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4146_: u64 = 0;
    let mut v___x_4147_: u64 = 0;
    let mut v___x_4148_: u64 = 0;
    let mut v_fold_4149_: u64 = 0;
    let mut v___x_4150_: u64 = 0;
    let mut v___x_4151_: u64 = 0;
    let mut v___x_4152_: u64 = 0;
    let mut v___x_4153_: usize = 0;
    let mut v___x_4154_: usize = 0;
    let mut v___x_4155_: usize = 0;
    let mut v___x_4156_: usize = 0;
    let mut v___x_4157_: usize = 0;
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: u64 = 0;
    let mut v_hash_4166_: u64 = 0;
    let mut v_isSharedCheck_4167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4137_) == 0 {
                    return v_x_4136_;
                } else {
                    v_key_4138_ = crate::leanh::lean_ctor_get(v_x_4137_, 0);
                    v_value_4139_ = crate::leanh::lean_ctor_get(v_x_4137_, 1);
                    v_tail_4140_ = crate::leanh::lean_ctor_get(v_x_4137_, 2);
                    v_isSharedCheck_4167_ = (!crate::leanh::lean_is_exclusive(v_x_4137_)) as u8;
                    if v_isSharedCheck_4167_ == 0 {
                        v___x_4142_ = v_x_4137_;
                        v_isShared_4143_ = v_isSharedCheck_4167_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4140_);
                        crate::leanh::lean_inc(v_value_4139_);
                        crate::leanh::lean_inc(v_key_4138_);
                        crate::leanh::lean_dec(v_x_4137_);
                        v___x_4142_ = crate::leanh::lean_box(0);
                        v_isShared_4143_ = v_isSharedCheck_4167_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4144_ = lean_array_get_size(v_x_4136_);
                v___x_4164_ = l_Lean_Meta_Grind_Origin_key(v_key_4138_);
                if crate::leanh::lean_obj_tag(v___x_4164_) == 0 {
                    v___x_4165_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0);
                    v___y_4146_ = v___x_4165_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4166_ = crate::leanh::lean_ctor_get_uint64(
                        v___x_4164_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___x_4164_);
                    v___y_4146_ = v_hash_4166_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4147_ = 32u64;
                v___x_4148_ = lean_uint64_shift_right(v___y_4146_, v___x_4147_);
                v_fold_4149_ = lean_uint64_xor(v___y_4146_, v___x_4148_);
                v___x_4150_ = 16u64;
                v___x_4151_ = lean_uint64_shift_right(v_fold_4149_, v___x_4150_);
                v___x_4152_ = lean_uint64_xor(v_fold_4149_, v___x_4151_);
                v___x_4153_ = lean_uint64_to_usize(v___x_4152_);
                v___x_4154_ = lean_usize_of_nat(v___x_4144_);
                v___x_4155_ = 1usize;
                v___x_4156_ = lean_usize_sub(v___x_4154_, v___x_4155_);
                v___x_4157_ = lean_usize_land(v___x_4153_, v___x_4156_);
                v___x_4158_ = lean_array_uget_borrowed(v_x_4136_, v___x_4157_);
                crate::leanh::lean_inc(v___x_4158_);
                if v_isShared_4143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4142_, 2, v___x_4158_);
                    v___x_4160_ = v___x_4142_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_key_4138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 1, v_value_4139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 2, v___x_4158_);
                    v___x_4160_ = v_reuseFailAlloc_4163_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4161_ = lean_array_uset(v_x_4136_, v___x_4157_, v___x_4160_);
                v_x_4136_ = v___x_4161_;
                v_x_4137_ = v_tail_4140_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2_spec__4___redArg(
    mut v_i_4168_: *mut crate::leanh::LeanObject,
    mut v_source_4169_: *mut crate::leanh::LeanObject,
    mut v_target_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: u8 = 0;
    let mut v_es_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4171_ = lean_array_get_size(v_source_4169_);
                v___x_4172_ = lean_nat_dec_lt(v_i_4168_, v___x_4171_);
                if v___x_4172_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4169_);
                    crate::leanh::lean_dec(v_i_4168_);
                    return v_target_4170_;
                } else {
                    v_es_4173_ = lean_array_fget(v_source_4169_, v_i_4168_);
                    v___x_4174_ = crate::leanh::lean_box(0);
                    v_source_4175_ = lean_array_fset(v_source_4169_, v_i_4168_, v___x_4174_);
                    v_target_4176_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2_spec__4_spec__6___redArg(v_target_4170_, v_es_4173_);
                    v___x_4177_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4178_ = lean_nat_add(v_i_4168_, v___x_4177_);
                    crate::leanh::lean_dec(v_i_4168_);
                    v_i_4168_ = v___x_4178_;
                    v_source_4169_ = v_source_4175_;
                    v_target_4170_ = v_target_4176_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2___redArg(
    mut v_data_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4181_ = lean_array_get_size(v_data_4180_);
    v___x_4182_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4183_ = lean_nat_mul(v___x_4181_, v___x_4182_);
    v___x_4184_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4185_ = crate::leanh::lean_box(0);
    v___x_4186_ = lean_mk_array(v_nbuckets_4183_, v___x_4185_);
    v___x_4187_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2_spec__4___redArg(v___x_4184_, v_data_4180_, v___x_4186_);
    return v___x_4187_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1___redArg(
    mut v_m_4188_: *mut crate::leanh::LeanObject,
    mut v_a_4189_: *mut crate::leanh::LeanObject,
    mut v_b_4190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4195_: u64 = 0;
    let mut v___x_4196_: u64 = 0;
    let mut v___x_4197_: u64 = 0;
    let mut v_fold_4198_: u64 = 0;
    let mut v___x_4199_: u64 = 0;
    let mut v___x_4200_: u64 = 0;
    let mut v___x_4201_: u64 = 0;
    let mut v___x_4202_: usize = 0;
    let mut v___x_4203_: usize = 0;
    let mut v___x_4204_: usize = 0;
    let mut v___x_4205_: usize = 0;
    let mut v___x_4206_: usize = 0;
    let mut v_bkt_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: u8 = 0;
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4211_: u8 = 0;
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: u8 = 0;
    let mut v_val_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4229_: u8 = 0;
    let mut v_unused_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: u64 = 0;
    let mut v_hash_4234_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4191_ = crate::leanh::lean_ctor_get(v_m_4188_, 0);
                v_buckets_4192_ = crate::leanh::lean_ctor_get(v_m_4188_, 1);
                v___x_4193_ = lean_array_get_size(v_buckets_4192_);
                v___x_4232_ = l_Lean_Meta_Grind_Origin_key(v_a_4189_);
                if crate::leanh::lean_obj_tag(v___x_4232_) == 0 {
                    v___x_4233_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect_go_spec__4_spec__8_spec__10_spec__12___redArg___closed__0);
                    v___y_4195_ = v___x_4233_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4234_ = crate::leanh::lean_ctor_get_uint64(
                        v___x_4232_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec(v___x_4232_);
                    v___y_4195_ = v_hash_4234_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4196_ = 32u64;
                v___x_4197_ = lean_uint64_shift_right(v___y_4195_, v___x_4196_);
                v_fold_4198_ = lean_uint64_xor(v___y_4195_, v___x_4197_);
                v___x_4199_ = 16u64;
                v___x_4200_ = lean_uint64_shift_right(v_fold_4198_, v___x_4199_);
                v___x_4201_ = lean_uint64_xor(v_fold_4198_, v___x_4200_);
                v___x_4202_ = lean_uint64_to_usize(v___x_4201_);
                v___x_4203_ = lean_usize_of_nat(v___x_4193_);
                v___x_4204_ = 1usize;
                v___x_4205_ = lean_usize_sub(v___x_4203_, v___x_4204_);
                v___x_4206_ = lean_usize_land(v___x_4202_, v___x_4205_);
                v_bkt_4207_ = lean_array_uget_borrowed(v_buckets_4192_, v___x_4206_);
                v___x_4208_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0_spec__0___redArg(v_a_4189_, v_bkt_4207_);
                if v___x_4208_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_4192_);
                    crate::leanh::lean_inc(v_size_4191_);
                    v_isSharedCheck_4229_ = (!crate::leanh::lean_is_exclusive(v_m_4188_)) as u8;
                    if v_isSharedCheck_4229_ == 0 {
                        v_unused_4230_ = crate::leanh::lean_ctor_get(v_m_4188_, 1);
                        crate::leanh::lean_dec(v_unused_4230_);
                        v_unused_4231_ = crate::leanh::lean_ctor_get(v_m_4188_, 0);
                        crate::leanh::lean_dec(v_unused_4231_);
                        v___x_4210_ = v_m_4188_;
                        v_isShared_4211_ = v_isSharedCheck_4229_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_4188_);
                        v___x_4210_ = crate::leanh::lean_box(0);
                        v_isShared_4211_ = v_isSharedCheck_4229_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_4190_);
                    crate::leanh::lean_dec_ref(v_a_4189_);
                    return v_m_4188_;
                }
            }
            2 => {
                v___x_4212_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_4213_ = lean_nat_add(v_size_4191_, v___x_4212_);
                crate::leanh::lean_dec(v_size_4191_);
                crate::leanh::lean_inc(v_bkt_4207_);
                v___x_4214_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4214_, 0, v_a_4189_);
                crate::leanh::lean_ctor_set(v___x_4214_, 1, v_b_4190_);
                crate::leanh::lean_ctor_set(v___x_4214_, 2, v_bkt_4207_);
                v_buckets_x27_4215_ = lean_array_uset(v_buckets_4192_, v___x_4206_, v___x_4214_);
                v___x_4216_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_4217_ = lean_nat_mul(v_size_x27_4213_, v___x_4216_);
                v___x_4218_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4219_ = lean_nat_div(v___x_4217_, v___x_4218_);
                crate::leanh::lean_dec(v___x_4217_);
                v___x_4220_ = lean_array_get_size(v_buckets_x27_4215_);
                v___x_4221_ = lean_nat_dec_le(v___x_4219_, v___x_4220_);
                crate::leanh::lean_dec(v___x_4219_);
                if v___x_4221_ == 0 {
                    v_val_4222_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2___redArg(v_buckets_x27_4215_);
                    if v_isShared_4211_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4210_, 1, v_val_4222_);
                        crate::leanh::lean_ctor_set(v___x_4210_, 0, v_size_x27_4213_);
                        v___x_4224_ = v___x_4210_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4225_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_size_x27_4213_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 1, v_val_4222_);
                        v___x_4224_ = v_reuseFailAlloc_4225_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_4211_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4210_, 1, v_buckets_x27_4215_);
                        crate::leanh::lean_ctor_set(v___x_4210_, 0, v_size_x27_4213_);
                        v___x_4227_ = v___x_4210_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4228_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_size_x27_4213_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 1, v_buckets_x27_4215_);
                        v___x_4227_ = v_reuseFailAlloc_4228_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4224_;
            }
            4 => {
                return v___x_4227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2(
    mut v_a_4246_: *mut crate::leanh::LeanObject,
    mut v_as_4247_: *mut crate::leanh::LeanObject,
    mut v_sz_4248_: usize,
    mut v_i_4249_: usize,
    mut v_b_4250_: *mut crate::leanh::LeanObject,
    mut v___y_4251_: *mut crate::leanh::LeanObject,
    mut v___y_4252_: *mut crate::leanh::LeanObject,
    mut v___y_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
    mut v___y_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
    mut v___y_4259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: usize = 0;
    let mut v___x_4264_: usize = 0;
    let mut v___x_4266_: u8 = 0;
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minIndexable_4272_: u8 = 0;
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: u8 = 0;
    let mut v_fst_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4281_: u8 = 0;
    let mut v_fst_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4286_: u8 = 0;
    let mut v_declName_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: u8 = 0;
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4328_: u8 = 0;
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4332_: u8 = 0;
    let mut v_a_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4336_: u8 = 0;
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4340_: u8 = 0;
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut v_isSharedCheck_4342_: u8 = 0;
    let mut v_unused_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4347_: u8 = 0;
    let mut v_fst_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4352_: u8 = 0;
    let mut v___x_4353_: u8 = 0;
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: u64 = 0;
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4381_: u8 = 0;
    let mut v_a_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4385_: u8 = 0;
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4389_: u8 = 0;
    let mut v_a_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4404_: u8 = 0;
    let mut v_isSharedCheck_4405_: u8 = 0;
    let mut v_unused_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v_fst_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4415_: u8 = 0;
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut v_unused_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4428_: u8 = 0;
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4266_ = lean_usize_dec_lt(v_i_4249_, v_sz_4248_);
                if v___x_4266_ == 0 {
                    v___x_4267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4267_, 0, v_b_4250_);
                    return v___x_4267_;
                } else {
                    v_a_4268_ = lean_array_uget_borrowed(v_as_4247_, v_i_4249_);
                    v_proof_4269_ = crate::leanh::lean_ctor_get(v_a_4268_, 1);
                    v_origin_4270_ = crate::leanh::lean_ctor_get(v_a_4268_, 5);
                    v_kind_4271_ = crate::leanh::lean_ctor_get(v_a_4268_, 6);
                    v_minIndexable_4272_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4268_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    v___x_4273_ = l_Lean_Meta_Grind_Origin_key(v_origin_4270_);
                    v___x_4274_ = l_Lean_Meta_Grind_isMatchEqLikeDeclName(
                        v___x_4273_,
                        v___y_4258_,
                        v___y_4259_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4274_) == 0 {
                        v_snd_4275_ = crate::leanh::lean_ctor_get(v_b_4250_, 1);
                        crate::leanh::lean_inc(v_snd_4275_);
                        v_a_4276_ = crate::leanh::lean_ctor_get(v___x_4274_, 0);
                        crate::leanh::lean_inc(v_a_4276_);
                        crate::leanh::lean_dec_ref_known(v___x_4274_, 1);
                        v___x_4277_ = (crate::leanh::lean_unbox(v_a_4276_) as u8);
                        crate::leanh::lean_dec(v_a_4276_);
                        if v___x_4277_ == 0 {
                            if crate::leanh::lean_obj_tag(v_origin_4270_) == 0 {
                                v_fst_4278_ = crate::leanh::lean_ctor_get(v_b_4250_, 0);
                                v_isSharedCheck_4342_ =
                                    (!crate::leanh::lean_is_exclusive(v_b_4250_)) as u8;
                                if v_isSharedCheck_4342_ == 0 {
                                    v_unused_4343_ = crate::leanh::lean_ctor_get(v_b_4250_, 1);
                                    crate::leanh::lean_dec(v_unused_4343_);
                                    v___x_4280_ = v_b_4250_;
                                    v_isShared_4281_ = v_isSharedCheck_4342_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_fst_4278_);
                                    crate::leanh::lean_dec(v_b_4250_);
                                    v___x_4280_ = crate::leanh::lean_box(0);
                                    v_isShared_4281_ = v_isSharedCheck_4342_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_fst_4344_ = crate::leanh::lean_ctor_get(v_b_4250_, 0);
                                v_isSharedCheck_4405_ =
                                    (!crate::leanh::lean_is_exclusive(v_b_4250_)) as u8;
                                if v_isSharedCheck_4405_ == 0 {
                                    v_unused_4406_ = crate::leanh::lean_ctor_get(v_b_4250_, 1);
                                    crate::leanh::lean_dec(v_unused_4406_);
                                    v___x_4346_ = v_b_4250_;
                                    v_isShared_4347_ = v_isSharedCheck_4405_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_fst_4344_);
                                    crate::leanh::lean_dec(v_b_4250_);
                                    v___x_4346_ = crate::leanh::lean_box(0);
                                    v_isShared_4347_ = v_isSharedCheck_4405_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            v_fst_4407_ = crate::leanh::lean_ctor_get(v_b_4250_, 0);
                            v_isSharedCheck_4423_ =
                                (!crate::leanh::lean_is_exclusive(v_b_4250_)) as u8;
                            if v_isSharedCheck_4423_ == 0 {
                                v_unused_4424_ = crate::leanh::lean_ctor_get(v_b_4250_, 1);
                                crate::leanh::lean_dec(v_unused_4424_);
                                v___x_4409_ = v_b_4250_;
                                v_isShared_4410_ = v_isSharedCheck_4423_;
                                state = 28;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_fst_4407_);
                                crate::leanh::lean_dec(v_b_4250_);
                                v___x_4409_ = crate::leanh::lean_box(0);
                                v_isShared_4410_ = v_isSharedCheck_4423_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4250_);
                        v_a_4425_ = crate::leanh::lean_ctor_get(v___x_4274_, 0);
                        v_isSharedCheck_4432_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4274_)) as u8;
                        if v_isSharedCheck_4432_ == 0 {
                            v___x_4427_ = v___x_4274_;
                            v_isShared_4428_ = v_isSharedCheck_4432_;
                            state = 32;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4425_);
                            crate::leanh::lean_dec(v___x_4274_);
                            v___x_4427_ = crate::leanh::lean_box(0);
                            v_isShared_4428_ = v_isSharedCheck_4432_;
                            state = 32;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4263_ = 1usize;
                v___x_4264_ = lean_usize_add(v_i_4249_, v___x_4263_);
                v_i_4249_ = v___x_4264_;
                v_b_4250_ = v_a_4262_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_4282_ = crate::leanh::lean_ctor_get(v_snd_4275_, 0);
                v_snd_4283_ = crate::leanh::lean_ctor_get(v_snd_4275_, 1);
                v_isSharedCheck_4341_ = (!crate::leanh::lean_is_exclusive(v_snd_4275_)) as u8;
                if v_isSharedCheck_4341_ == 0 {
                    v___x_4285_ = v_snd_4275_;
                    v_isShared_4286_ = v_isSharedCheck_4341_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4283_);
                    crate::leanh::lean_inc(v_fst_4282_);
                    crate::leanh::lean_dec(v_snd_4275_);
                    v___x_4285_ = crate::leanh::lean_box(0);
                    v_isShared_4286_ = v_isSharedCheck_4341_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_declName_4287_ = crate::leanh::lean_ctor_get(v_origin_4270_, 0);
                v___x_4288_ = l_Lean_Meta_isEqnThm_x3f___redArg(v_declName_4287_, v___y_4259_);
                if crate::leanh::lean_obj_tag(v___x_4288_) == 0 {
                    v_a_4289_ = crate::leanh::lean_ctor_get(v___x_4288_, 0);
                    crate::leanh::lean_inc(v_a_4289_);
                    crate::leanh::lean_dec_ref_known(v___x_4288_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4289_) == 1 {
                        v_val_4290_ = crate::leanh::lean_ctor_get(v_a_4289_, 0);
                        crate::leanh::lean_inc(v_val_4290_);
                        crate::leanh::lean_dec_ref_known(v_a_4289_, 1);
                        v___x_4291_ = l_Lean_NameSet_contains(v_fst_4282_, v_val_4290_);
                        if v___x_4291_ == 0 {
                            crate::leanh::lean_inc(v_declName_4287_);
                            v___x_4292_ = l_Lean_Meta_Grind_globalDeclToInstantiateParamSyntax(
                                v_declName_4287_,
                                v_kind_4271_,
                                v_minIndexable_4272_,
                                v___y_4256_,
                                v___y_4257_,
                                v___y_4258_,
                                v___y_4259_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4292_) == 0 {
                                v_a_4293_ = crate::leanh::lean_ctor_get(v___x_4292_, 0);
                                crate::leanh::lean_inc(v_a_4293_);
                                crate::leanh::lean_dec_ref_known(v___x_4292_, 1);
                                v___x_4294_ = l_Lean_NameSet_insert(v_fst_4282_, v_val_4290_);
                                v___x_4295_ = lean_array_push(v_fst_4278_, v_a_4293_);
                                if v_isShared_4286_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_4285_, 0, v___x_4294_);
                                    v___x_4297_ = v___x_4285_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4301_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4301_,
                                        0,
                                        v___x_4294_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4301_,
                                        1,
                                        v_snd_4283_,
                                    );
                                    v___x_4297_ = v_reuseFailAlloc_4301_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_4290_);
                                crate::leanh::lean_del_object(v___x_4285_);
                                crate::leanh::lean_dec(v_snd_4283_);
                                crate::leanh::lean_dec(v_fst_4282_);
                                crate::leanh::lean_del_object(v___x_4280_);
                                crate::leanh::lean_dec(v_fst_4278_);
                                v_a_4302_ = crate::leanh::lean_ctor_get(v___x_4292_, 0);
                                v_isSharedCheck_4309_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4292_)) as u8;
                                if v_isSharedCheck_4309_ == 0 {
                                    v___x_4304_ = v___x_4292_;
                                    v_isShared_4305_ = v_isSharedCheck_4309_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4302_);
                                    crate::leanh::lean_dec(v___x_4292_);
                                    v___x_4304_ = crate::leanh::lean_box(0);
                                    v_isShared_4305_ = v_isSharedCheck_4309_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_4290_);
                            if v_isShared_4286_ == 0 {
                                v___x_4311_ = v___x_4285_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_4315_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_fst_4282_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4315_, 1, v_snd_4283_);
                                v___x_4311_ = v_reuseFailAlloc_4315_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4289_);
                        crate::leanh::lean_inc(v_declName_4287_);
                        v___x_4316_ = l_Lean_Meta_Grind_globalDeclToInstantiateParamSyntax(
                            v_declName_4287_,
                            v_kind_4271_,
                            v_minIndexable_4272_,
                            v___y_4256_,
                            v___y_4257_,
                            v___y_4258_,
                            v___y_4259_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4316_) == 0 {
                            v_a_4317_ = crate::leanh::lean_ctor_get(v___x_4316_, 0);
                            crate::leanh::lean_inc(v_a_4317_);
                            crate::leanh::lean_dec_ref_known(v___x_4316_, 1);
                            v___x_4318_ = lean_array_push(v_fst_4278_, v_a_4317_);
                            if v_isShared_4286_ == 0 {
                                v___x_4320_ = v___x_4285_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4324_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_fst_4282_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4324_, 1, v_snd_4283_);
                                v___x_4320_ = v_reuseFailAlloc_4324_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4285_);
                            crate::leanh::lean_dec(v_snd_4283_);
                            crate::leanh::lean_dec(v_fst_4282_);
                            crate::leanh::lean_del_object(v___x_4280_);
                            crate::leanh::lean_dec(v_fst_4278_);
                            v_a_4325_ = crate::leanh::lean_ctor_get(v___x_4316_, 0);
                            v_isSharedCheck_4332_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4316_)) as u8;
                            if v_isSharedCheck_4332_ == 0 {
                                v___x_4327_ = v___x_4316_;
                                v_isShared_4328_ = v_isSharedCheck_4332_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4325_);
                                crate::leanh::lean_dec(v___x_4316_);
                                v___x_4327_ = crate::leanh::lean_box(0);
                                v_isShared_4328_ = v_isSharedCheck_4332_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4285_);
                    crate::leanh::lean_dec(v_snd_4283_);
                    crate::leanh::lean_dec(v_fst_4282_);
                    crate::leanh::lean_del_object(v___x_4280_);
                    crate::leanh::lean_dec(v_fst_4278_);
                    v_a_4333_ = crate::leanh::lean_ctor_get(v___x_4288_, 0);
                    v_isSharedCheck_4340_ = (!crate::leanh::lean_is_exclusive(v___x_4288_)) as u8;
                    if v_isSharedCheck_4340_ == 0 {
                        v___x_4335_ = v___x_4288_;
                        v_isShared_4336_ = v_isSharedCheck_4340_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4333_);
                        crate::leanh::lean_dec(v___x_4288_);
                        v___x_4335_ = crate::leanh::lean_box(0);
                        v_isShared_4336_ = v_isSharedCheck_4340_;
                        state = 14;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4281_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4280_, 1, v___x_4297_);
                    crate::leanh::lean_ctor_set(v___x_4280_, 0, v___x_4295_);
                    v___x_4299_ = v___x_4280_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4300_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 1, v___x_4297_);
                    v___x_4299_ = v_reuseFailAlloc_4300_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_4262_ = v___x_4299_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_4305_ == 0 {
                    v___x_4307_ = v___x_4304_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
                    v___x_4307_ = v_reuseFailAlloc_4308_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4307_;
            }
            8 => {
                if v_isShared_4281_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4280_, 1, v___x_4311_);
                    v___x_4313_ = v___x_4280_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4314_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_fst_4278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4314_, 1, v___x_4311_);
                    v___x_4313_ = v_reuseFailAlloc_4314_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_4262_ = v___x_4313_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_4281_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4280_, 1, v___x_4320_);
                    crate::leanh::lean_ctor_set(v___x_4280_, 0, v___x_4318_);
                    v___x_4322_ = v___x_4280_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4323_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4323_, 1, v___x_4320_);
                    v___x_4322_ = v_reuseFailAlloc_4323_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_4262_ = v___x_4322_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_4328_ == 0 {
                    v___x_4330_ = v___x_4327_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4331_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
                    v___x_4330_ = v_reuseFailAlloc_4331_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4330_;
            }
            14 => {
                if v_isShared_4336_ == 0 {
                    v___x_4338_ = v___x_4335_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4339_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
                    v___x_4338_ = v_reuseFailAlloc_4339_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4338_;
            }
            16 => {
                v_fst_4348_ = crate::leanh::lean_ctor_get(v_snd_4275_, 0);
                v_snd_4349_ = crate::leanh::lean_ctor_get(v_snd_4275_, 1);
                v_isSharedCheck_4404_ = (!crate::leanh::lean_is_exclusive(v_snd_4275_)) as u8;
                if v_isSharedCheck_4404_ == 0 {
                    v___x_4351_ = v_snd_4275_;
                    v_isShared_4352_ = v_isSharedCheck_4404_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4349_);
                    crate::leanh::lean_inc(v_fst_4348_);
                    crate::leanh::lean_dec(v_snd_4275_);
                    v___x_4351_ = crate::leanh::lean_box(0);
                    v_isShared_4352_ = v_isSharedCheck_4404_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4353_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0___redArg(v_snd_4349_, v_origin_4270_);
                if v___x_4353_ == 0 {
                    crate::leanh::lean_inc(v___y_4259_);
                    crate::leanh::lean_inc_ref(v___y_4258_);
                    crate::leanh::lean_inc(v___y_4257_);
                    crate::leanh::lean_inc_ref(v___y_4256_);
                    crate::leanh::lean_inc_ref(v_proof_4269_);
                    v___x_4354_ = lean_infer_type(
                        v_proof_4269_,
                        v___y_4256_,
                        v___y_4257_,
                        v___y_4258_,
                        v___y_4259_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4354_) == 0 {
                        v_a_4355_ = crate::leanh::lean_ctor_get(v___x_4354_, 0);
                        crate::leanh::lean_inc(v_a_4355_);
                        crate::leanh::lean_dec_ref_known(v___x_4354_, 1);
                        v___x_4356_ = l_Lean_Meta_Grind_getAnchor(
                            v_a_4355_,
                            v___y_4251_,
                            v___y_4252_,
                            v___y_4253_,
                            v___y_4254_,
                            v___y_4255_,
                            v___y_4256_,
                            v___y_4257_,
                            v___y_4258_,
                            v___y_4259_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4356_) == 0 {
                            v_a_4357_ = crate::leanh::lean_ctor_get(v___x_4356_, 0);
                            crate::leanh::lean_inc(v_a_4357_);
                            crate::leanh::lean_dec_ref_known(v___x_4356_, 1);
                            v___x_4358_ = crate::leanh::lean_unbox_uint64(v_a_4357_);
                            crate::leanh::lean_dec(v_a_4357_);
                            v___x_4359_ = l_Lean_Meta_Grind_mkAnchorSyntax___redArg(
                                v_a_4246_,
                                v___x_4358_,
                                v___y_4258_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4359_) == 0 {
                                v_a_4360_ = crate::leanh::lean_ctor_get(v___x_4359_, 0);
                                crate::leanh::lean_inc(v_a_4360_);
                                crate::leanh::lean_dec_ref_known(v___x_4359_, 1);
                                v_ref_4361_ = crate::leanh::lean_ctor_get(v___y_4258_, 5);
                                v___x_4362_ = crate::leanh::lean_box(0);
                                crate::leanh::lean_inc_ref(v_origin_4270_);
                                v___x_4363_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1___redArg(v_snd_4349_, v_origin_4270_, v___x_4362_);
                                v___x_4364_ = l_Lean_SourceInfo_fromRef(v_ref_4361_, v___x_4353_);
                                v___x_4365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___closed__5;
                                v___x_4366_ =
                                    l_Lean_Syntax_node1(v___x_4364_, v___x_4365_, v_a_4360_);
                                v___x_4367_ = lean_array_push(v_fst_4344_, v___x_4366_);
                                if v_isShared_4352_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_4351_, 1, v___x_4363_);
                                    v___x_4369_ = v___x_4351_;
                                    state = 18;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4373_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4373_,
                                        0,
                                        v_fst_4348_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4373_,
                                        1,
                                        v___x_4363_,
                                    );
                                    v___x_4369_ = v_reuseFailAlloc_4373_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_4351_);
                                crate::leanh::lean_dec(v_snd_4349_);
                                crate::leanh::lean_dec(v_fst_4348_);
                                crate::leanh::lean_del_object(v___x_4346_);
                                crate::leanh::lean_dec(v_fst_4344_);
                                v_a_4374_ = crate::leanh::lean_ctor_get(v___x_4359_, 0);
                                v_isSharedCheck_4381_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4359_)) as u8;
                                if v_isSharedCheck_4381_ == 0 {
                                    v___x_4376_ = v___x_4359_;
                                    v_isShared_4377_ = v_isSharedCheck_4381_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4374_);
                                    crate::leanh::lean_dec(v___x_4359_);
                                    v___x_4376_ = crate::leanh::lean_box(0);
                                    v_isShared_4377_ = v_isSharedCheck_4381_;
                                    state = 20;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4351_);
                            crate::leanh::lean_dec(v_snd_4349_);
                            crate::leanh::lean_dec(v_fst_4348_);
                            crate::leanh::lean_del_object(v___x_4346_);
                            crate::leanh::lean_dec(v_fst_4344_);
                            v_a_4382_ = crate::leanh::lean_ctor_get(v___x_4356_, 0);
                            v_isSharedCheck_4389_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4356_)) as u8;
                            if v_isSharedCheck_4389_ == 0 {
                                v___x_4384_ = v___x_4356_;
                                v_isShared_4385_ = v_isSharedCheck_4389_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4382_);
                                crate::leanh::lean_dec(v___x_4356_);
                                v___x_4384_ = crate::leanh::lean_box(0);
                                v_isShared_4385_ = v_isSharedCheck_4389_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4351_);
                        crate::leanh::lean_dec(v_snd_4349_);
                        crate::leanh::lean_dec(v_fst_4348_);
                        crate::leanh::lean_del_object(v___x_4346_);
                        crate::leanh::lean_dec(v_fst_4344_);
                        v_a_4390_ = crate::leanh::lean_ctor_get(v___x_4354_, 0);
                        v_isSharedCheck_4397_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4354_)) as u8;
                        if v_isSharedCheck_4397_ == 0 {
                            v___x_4392_ = v___x_4354_;
                            v_isShared_4393_ = v_isSharedCheck_4397_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4390_);
                            crate::leanh::lean_dec(v___x_4354_);
                            v___x_4392_ = crate::leanh::lean_box(0);
                            v_isShared_4393_ = v_isSharedCheck_4397_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    if v_isShared_4352_ == 0 {
                        v___x_4399_ = v___x_4351_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_4403_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_fst_4348_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4403_, 1, v_snd_4349_);
                        v___x_4399_ = v_reuseFailAlloc_4403_;
                        state = 26;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_4347_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4346_, 1, v___x_4369_);
                    crate::leanh::lean_ctor_set(v___x_4346_, 0, v___x_4367_);
                    v___x_4371_ = v___x_4346_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4372_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4372_, 0, v___x_4367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4372_, 1, v___x_4369_);
                    v___x_4371_ = v_reuseFailAlloc_4372_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v_a_4262_ = v___x_4371_;
                state = 1;
                continue;
            }
            20 => {
                if v_isShared_4377_ == 0 {
                    v___x_4379_ = v___x_4376_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
                    v___x_4379_ = v_reuseFailAlloc_4380_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4379_;
            }
            22 => {
                if v_isShared_4385_ == 0 {
                    v___x_4387_ = v___x_4384_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
                    v___x_4387_ = v_reuseFailAlloc_4388_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4387_;
            }
            24 => {
                if v_isShared_4393_ == 0 {
                    v___x_4395_ = v___x_4392_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
                    v___x_4395_ = v_reuseFailAlloc_4396_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4395_;
            }
            26 => {
                if v_isShared_4347_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4346_, 1, v___x_4399_);
                    v___x_4401_ = v___x_4346_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4402_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_fst_4344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 1, v___x_4399_);
                    v___x_4401_ = v_reuseFailAlloc_4402_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v_a_4262_ = v___x_4401_;
                state = 1;
                continue;
            }
            28 => {
                v_fst_4411_ = crate::leanh::lean_ctor_get(v_snd_4275_, 0);
                v_snd_4412_ = crate::leanh::lean_ctor_get(v_snd_4275_, 1);
                v_isSharedCheck_4422_ = (!crate::leanh::lean_is_exclusive(v_snd_4275_)) as u8;
                if v_isSharedCheck_4422_ == 0 {
                    v___x_4414_ = v_snd_4275_;
                    v_isShared_4415_ = v_isSharedCheck_4422_;
                    state = 29;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4412_);
                    crate::leanh::lean_inc(v_fst_4411_);
                    crate::leanh::lean_dec(v_snd_4275_);
                    v___x_4414_ = crate::leanh::lean_box(0);
                    v_isShared_4415_ = v_isSharedCheck_4422_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_4415_ == 0 {
                    v___x_4417_ = v___x_4414_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4421_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_fst_4411_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 1, v_snd_4412_);
                    v___x_4417_ = v_reuseFailAlloc_4421_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_4410_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4409_, 1, v___x_4417_);
                    v___x_4419_ = v___x_4409_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4420_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_fst_4407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4420_, 1, v___x_4417_);
                    v___x_4419_ = v_reuseFailAlloc_4420_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v_a_4262_ = v___x_4419_;
                state = 1;
                continue;
            }
            32 => {
                if v_isShared_4428_ == 0 {
                    v___x_4430_ = v___x_4427_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4431_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
                    v___x_4430_ = v_reuseFailAlloc_4431_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2___boxed(
    mut v_a_4433_: *mut crate::leanh::LeanObject,
    mut v_as_4434_: *mut crate::leanh::LeanObject,
    mut v_sz_4435_: *mut crate::leanh::LeanObject,
    mut v_i_4436_: *mut crate::leanh::LeanObject,
    mut v_b_4437_: *mut crate::leanh::LeanObject,
    mut v___y_4438_: *mut crate::leanh::LeanObject,
    mut v___y_4439_: *mut crate::leanh::LeanObject,
    mut v___y_4440_: *mut crate::leanh::LeanObject,
    mut v___y_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
    mut v___y_4443_: *mut crate::leanh::LeanObject,
    mut v___y_4444_: *mut crate::leanh::LeanObject,
    mut v___y_4445_: *mut crate::leanh::LeanObject,
    mut v___y_4446_: *mut crate::leanh::LeanObject,
    mut v___y_4447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4448_: usize = 0;
    let mut v_i_boxed_4449_: usize = 0;
    let mut v_res_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4448_ = crate::leanh::lean_unbox_usize(v_sz_4435_);
    crate::leanh::lean_dec(v_sz_4435_);
    v_i_boxed_4449_ = crate::leanh::lean_unbox_usize(v_i_4436_);
    crate::leanh::lean_dec(v_i_4436_);
    v_res_4450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2(v_a_4433_, v_as_4434_, v_sz_boxed_4448_, v_i_boxed_4449_, v_b_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
    crate::leanh::lean_dec(v___y_4446_);
    crate::leanh::lean_dec_ref(v___y_4445_);
    crate::leanh::lean_dec(v___y_4444_);
    crate::leanh::lean_dec_ref(v___y_4443_);
    crate::leanh::lean_dec(v___y_4442_);
    crate::leanh::lean_dec_ref(v___y_4441_);
    crate::leanh::lean_dec(v___y_4440_);
    crate::leanh::lean_dec_ref(v___y_4439_);
    crate::leanh::lean_dec(v___y_4438_);
    crate::leanh::lean_dec_ref(v_as_4434_);
    crate::leanh::lean_dec(v_a_4433_);
    return v_res_4450_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4453_ = crate::leanh::lean_box(0);
    v___x_4454_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4455_ = lean_mk_array(v___x_4454_, v___x_4453_);
    return v___x_4455_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundLocals_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__1);
    v___x_4457_ = crate::leanh::lean_unsigned_to_nat(0);
    v_foundLocals_4458_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_foundLocals_4458_, 0, v___x_4457_);
    crate::leanh::lean_ctor_set(v_foundLocals_4458_, 1, v___x_4456_);
    return v_foundLocals_4458_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v_foundLocals_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foundFns_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_foundLocals_4459_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__2);
    v_foundFns_4460_ = l_Lean_NameSet_empty;
    v___x_4461_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4461_, 0, v_foundFns_4460_);
    crate::leanh::lean_ctor_set(v___x_4461_, 1, v_foundLocals_4459_);
    return v___x_4461_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4462_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__3);
    v_params_4463_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__0;
    v___x_4464_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4464_, 0, v_params_4463_);
    crate::leanh::lean_ctor_set(v___x_4464_, 1, v___x_4462_);
    return v___x_4464_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4476_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_4476_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0(
    mut v_goal_4481_: *mut crate::leanh::LeanObject,
    mut v_usedThms_4482_: *mut crate::leanh::LeanObject,
    mut v_approx_4483_: u8,
    mut v___y_4484_: *mut crate::leanh::LeanObject,
    mut v___y_4485_: *mut crate::leanh::LeanObject,
    mut v___y_4486_: *mut crate::leanh::LeanObject,
    mut v___y_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
    mut v___y_4489_: *mut crate::leanh::LeanObject,
    mut v___y_4490_: *mut crate::leanh::LeanObject,
    mut v___y_4491_: *mut crate::leanh::LeanObject,
    mut v___y_4492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4498_: usize = 0;
    let mut v___x_4499_: usize = 0;
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4504_: u8 = 0;
    let mut v_fst_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4508_: u8 = 0;
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: u8 = 0;
    let mut v_ref_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: u8 = 0;
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4600_: u8 = 0;
    let mut v_unused_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4602_: u8 = 0;
    let mut v_a_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4606_: u8 = 0;
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut v_a_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4494_ = l_Lean_Meta_Grind_getNumDigitsForLocalTheoremAnchors(
                    v_goal_4481_,
                    v___y_4484_,
                    v___y_4485_,
                    v___y_4486_,
                    v___y_4487_,
                    v___y_4488_,
                    v___y_4489_,
                    v___y_4490_,
                    v___y_4491_,
                    v___y_4492_,
                );
                if crate::leanh::lean_obj_tag(v___x_4494_) == 0 {
                    v_a_4495_ = crate::leanh::lean_ctor_get(v___x_4494_, 0);
                    crate::leanh::lean_inc(v_a_4495_);
                    crate::leanh::lean_dec_ref_known(v___x_4494_, 1);
                    v___x_4496_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4497_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__4);
                    v_sz_4498_ = lean_array_size(v_usedThms_4482_);
                    v___x_4499_ = 0usize;
                    v___x_4500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__2(v_a_4495_, v_usedThms_4482_, v_sz_4498_, v___x_4499_, v___x_4497_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
                    crate::leanh::lean_dec(v_a_4495_);
                    if crate::leanh::lean_obj_tag(v___x_4500_) == 0 {
                        v_a_4501_ = crate::leanh::lean_ctor_get(v___x_4500_, 0);
                        v_isSharedCheck_4602_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4500_)) as u8;
                        if v_isSharedCheck_4602_ == 0 {
                            v___x_4503_ = v___x_4500_;
                            v_isShared_4504_ = v_isSharedCheck_4602_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4501_);
                            crate::leanh::lean_dec(v___x_4500_);
                            v___x_4503_ = crate::leanh::lean_box(0);
                            v_isShared_4504_ = v_isSharedCheck_4602_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4603_ = crate::leanh::lean_ctor_get(v___x_4500_, 0);
                        v_isSharedCheck_4610_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4500_)) as u8;
                        if v_isSharedCheck_4610_ == 0 {
                            v___x_4605_ = v___x_4500_;
                            v_isShared_4606_ = v_isSharedCheck_4610_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4603_);
                            crate::leanh::lean_dec(v___x_4500_);
                            v___x_4605_ = crate::leanh::lean_box(0);
                            v_isShared_4606_ = v_isSharedCheck_4610_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    v_a_4611_ = crate::leanh::lean_ctor_get(v___x_4494_, 0);
                    v_isSharedCheck_4618_ = (!crate::leanh::lean_is_exclusive(v___x_4494_)) as u8;
                    if v_isSharedCheck_4618_ == 0 {
                        v___x_4613_ = v___x_4494_;
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4611_);
                        crate::leanh::lean_dec(v___x_4494_);
                        v___x_4613_ = crate::leanh::lean_box(0);
                        v_isShared_4614_ = v_isSharedCheck_4618_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4505_ = crate::leanh::lean_ctor_get(v_a_4501_, 0);
                v_isSharedCheck_4600_ = (!crate::leanh::lean_is_exclusive(v_a_4501_)) as u8;
                if v_isSharedCheck_4600_ == 0 {
                    v_unused_4601_ = crate::leanh::lean_ctor_get(v_a_4501_, 1);
                    crate::leanh::lean_dec(v_unused_4601_);
                    v___x_4507_ = v_a_4501_;
                    v_isShared_4508_ = v_isSharedCheck_4600_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_4505_);
                    crate::leanh::lean_dec(v_a_4501_);
                    v___x_4507_ = crate::leanh::lean_box(0);
                    v_isShared_4508_ = v_isSharedCheck_4600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4509_ = lean_array_get_size(v_fst_4505_);
                v___x_4510_ = lean_nat_dec_eq(v___x_4509_, v___x_4496_);
                if v___x_4510_ == 0 {
                    if v_approx_4483_ == 0 {
                        v_ref_4511_ = crate::leanh::lean_ctor_get(v___y_4491_, 5);
                        v___x_4512_ = l_Lean_SourceInfo_fromRef(v_ref_4511_, v_approx_4483_);
                        v___x_4513_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__5;
                        v___x_4514_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6;
                        crate::leanh::lean_inc(v___x_4512_);
                        if v_isShared_4508_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4507_, 2);
                            crate::leanh::lean_ctor_set(v___x_4507_, 1, v___x_4513_);
                            crate::leanh::lean_ctor_set(v___x_4507_, 0, v___x_4512_);
                            v___x_4516_ = v___x_4507_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4536_ =
                                crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4512_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 1, v___x_4513_);
                            v___x_4516_ = v_reuseFailAlloc_4536_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_ref_4537_ = crate::leanh::lean_ctor_get(v___y_4491_, 5);
                        v___x_4538_ = l_Lean_SourceInfo_fromRef(v_ref_4537_, v___x_4510_);
                        v___x_4539_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__5;
                        v___x_4540_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6;
                        crate::leanh::lean_inc(v___x_4538_);
                        if v_isShared_4508_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4507_, 2);
                            crate::leanh::lean_ctor_set(v___x_4507_, 1, v___x_4539_);
                            crate::leanh::lean_ctor_set(v___x_4507_, 0, v___x_4538_);
                            v___x_4542_ = v___x_4507_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_4564_ =
                                crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4538_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 1, v___x_4539_);
                            v___x_4542_ = v_reuseFailAlloc_4564_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_4505_);
                    if v_approx_4483_ == 0 {
                        v_ref_4565_ = crate::leanh::lean_ctor_get(v___y_4491_, 5);
                        v___x_4566_ = l_Lean_SourceInfo_fromRef(v_ref_4565_, v_approx_4483_);
                        v___x_4567_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__5;
                        v___x_4568_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6;
                        crate::leanh::lean_inc(v___x_4566_);
                        if v_isShared_4508_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4507_, 2);
                            crate::leanh::lean_ctor_set(v___x_4507_, 1, v___x_4567_);
                            crate::leanh::lean_ctor_set(v___x_4507_, 0, v___x_4566_);
                            v___x_4570_ = v___x_4507_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_4581_ =
                                crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4581_, 0, v___x_4566_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4581_, 1, v___x_4567_);
                            v___x_4570_ = v_reuseFailAlloc_4581_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_ref_4582_ = crate::leanh::lean_ctor_get(v___y_4491_, 5);
                        v___x_4583_ = 0;
                        v___x_4584_ = l_Lean_SourceInfo_fromRef(v_ref_4582_, v___x_4583_);
                        v___x_4585_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__5;
                        v___x_4586_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__6;
                        crate::leanh::lean_inc(v___x_4584_);
                        if v_isShared_4508_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4507_, 2);
                            crate::leanh::lean_ctor_set(v___x_4507_, 1, v___x_4585_);
                            crate::leanh::lean_ctor_set(v___x_4507_, 0, v___x_4584_);
                            v___x_4588_ = v___x_4507_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_4599_ =
                                crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4584_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4599_, 1, v___x_4585_);
                            v___x_4588_ = v_reuseFailAlloc_4599_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_4517_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__8;
                v___x_4518_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__9;
                crate::leanh::lean_inc_n(v___x_4512_, 7);
                v___x_4519_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4519_, 0, v___x_4512_);
                crate::leanh::lean_ctor_set(v___x_4519_, 1, v___x_4518_);
                v___x_4520_ = l_Lean_Syntax_node1(v___x_4512_, v___x_4517_, v___x_4519_);
                v___x_4521_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10);
                v___x_4522_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4522_, 0, v___x_4512_);
                crate::leanh::lean_ctor_set(v___x_4522_, 1, v___x_4517_);
                crate::leanh::lean_ctor_set(v___x_4522_, 2, v___x_4521_);
                v___x_4523_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__11;
                v___x_4524_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4524_, 0, v___x_4512_);
                crate::leanh::lean_ctor_set(v___x_4524_, 1, v___x_4523_);
                v___x_4525_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__12;
                v___x_4526_ = l_Lean_Syntax_SepArray_ofElems(v___x_4525_, v_fst_4505_);
                crate::leanh::lean_dec(v_fst_4505_);
                v___x_4527_ = l_Array_append___redArg(v___x_4521_, v___x_4526_);
                crate::leanh::lean_dec_ref(v___x_4526_);
                v___x_4528_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4528_, 0, v___x_4512_);
                crate::leanh::lean_ctor_set(v___x_4528_, 1, v___x_4517_);
                crate::leanh::lean_ctor_set(v___x_4528_, 2, v___x_4527_);
                v___x_4529_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__13;
                v___x_4530_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4530_, 0, v___x_4512_);
                crate::leanh::lean_ctor_set(v___x_4530_, 1, v___x_4529_);
                v___x_4531_ = l_Lean_Syntax_node3(
                    v___x_4512_,
                    v___x_4517_,
                    v___x_4524_,
                    v___x_4528_,
                    v___x_4530_,
                );
                v___x_4532_ = l_Lean_Syntax_node4(
                    v___x_4512_,
                    v___x_4514_,
                    v___x_4516_,
                    v___x_4520_,
                    v___x_4522_,
                    v___x_4531_,
                );
                if v_isShared_4504_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4503_, 0, v___x_4532_);
                    v___x_4534_ = v___x_4503_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4535_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4532_);
                    v___x_4534_ = v_reuseFailAlloc_4535_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4534_;
            }
            5 => {
                v___x_4543_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__8;
                v___x_4544_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__9;
                crate::leanh::lean_inc_n(v___x_4538_, 8);
                v___x_4545_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4545_, 0, v___x_4538_);
                crate::leanh::lean_ctor_set(v___x_4545_, 1, v___x_4544_);
                v___x_4546_ = l_Lean_Syntax_node1(v___x_4538_, v___x_4543_, v___x_4545_);
                v___x_4547_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__14;
                v___x_4548_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4548_, 0, v___x_4538_);
                crate::leanh::lean_ctor_set(v___x_4548_, 1, v___x_4547_);
                v___x_4549_ = l_Lean_Syntax_node1(v___x_4538_, v___x_4543_, v___x_4548_);
                v___x_4550_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__11;
                v___x_4551_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4551_, 0, v___x_4538_);
                crate::leanh::lean_ctor_set(v___x_4551_, 1, v___x_4550_);
                v___x_4552_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10);
                v___x_4553_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__12;
                v___x_4554_ = l_Lean_Syntax_SepArray_ofElems(v___x_4553_, v_fst_4505_);
                crate::leanh::lean_dec(v_fst_4505_);
                v___x_4555_ = l_Array_append___redArg(v___x_4552_, v___x_4554_);
                crate::leanh::lean_dec_ref(v___x_4554_);
                v___x_4556_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4556_, 0, v___x_4538_);
                crate::leanh::lean_ctor_set(v___x_4556_, 1, v___x_4543_);
                crate::leanh::lean_ctor_set(v___x_4556_, 2, v___x_4555_);
                v___x_4557_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__13;
                v___x_4558_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4558_, 0, v___x_4538_);
                crate::leanh::lean_ctor_set(v___x_4558_, 1, v___x_4557_);
                v___x_4559_ = l_Lean_Syntax_node3(
                    v___x_4538_,
                    v___x_4543_,
                    v___x_4551_,
                    v___x_4556_,
                    v___x_4558_,
                );
                v___x_4560_ = l_Lean_Syntax_node4(
                    v___x_4538_,
                    v___x_4540_,
                    v___x_4542_,
                    v___x_4546_,
                    v___x_4549_,
                    v___x_4559_,
                );
                if v_isShared_4504_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4503_, 0, v___x_4560_);
                    v___x_4562_ = v___x_4503_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4563_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4563_, 0, v___x_4560_);
                    v___x_4562_ = v_reuseFailAlloc_4563_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4562_;
            }
            7 => {
                v___x_4571_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__8;
                v___x_4572_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__9;
                crate::leanh::lean_inc_n(v___x_4566_, 3);
                v___x_4573_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4573_, 0, v___x_4566_);
                crate::leanh::lean_ctor_set(v___x_4573_, 1, v___x_4572_);
                v___x_4574_ = l_Lean_Syntax_node1(v___x_4566_, v___x_4571_, v___x_4573_);
                v___x_4575_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10);
                v___x_4576_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4576_, 0, v___x_4566_);
                crate::leanh::lean_ctor_set(v___x_4576_, 1, v___x_4571_);
                crate::leanh::lean_ctor_set(v___x_4576_, 2, v___x_4575_);
                crate::leanh::lean_inc_ref(v___x_4576_);
                v___x_4577_ = l_Lean_Syntax_node4(
                    v___x_4566_,
                    v___x_4568_,
                    v___x_4570_,
                    v___x_4574_,
                    v___x_4576_,
                    v___x_4576_,
                );
                if v_isShared_4504_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4503_, 0, v___x_4577_);
                    v___x_4579_ = v___x_4503_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4580_, 0, v___x_4577_);
                    v___x_4579_ = v_reuseFailAlloc_4580_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4579_;
            }
            9 => {
                v___x_4589_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__8;
                v___x_4590_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__10);
                crate::leanh::lean_inc_n(v___x_4584_, 3);
                v___x_4591_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4591_, 0, v___x_4584_);
                crate::leanh::lean_ctor_set(v___x_4591_, 1, v___x_4589_);
                crate::leanh::lean_ctor_set(v___x_4591_, 2, v___x_4590_);
                v___x_4592_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___closed__14;
                v___x_4593_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4593_, 0, v___x_4584_);
                crate::leanh::lean_ctor_set(v___x_4593_, 1, v___x_4592_);
                v___x_4594_ = l_Lean_Syntax_node1(v___x_4584_, v___x_4589_, v___x_4593_);
                crate::leanh::lean_inc_ref(v___x_4591_);
                v___x_4595_ = l_Lean_Syntax_node4(
                    v___x_4584_,
                    v___x_4586_,
                    v___x_4588_,
                    v___x_4591_,
                    v___x_4594_,
                    v___x_4591_,
                );
                if v_isShared_4504_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4503_, 0, v___x_4595_);
                    v___x_4597_ = v___x_4503_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4595_);
                    v___x_4597_ = v_reuseFailAlloc_4598_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4597_;
            }
            11 => {
                if v_isShared_4606_ == 0 {
                    v___x_4608_ = v___x_4605_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
                    v___x_4608_ = v_reuseFailAlloc_4609_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4608_;
            }
            13 => {
                if v_isShared_4614_ == 0 {
                    v___x_4616_ = v___x_4613_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4617_, 0, v_a_4611_);
                    v___x_4616_ = v_reuseFailAlloc_4617_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___boxed(
    mut v_goal_4619_: *mut crate::leanh::LeanObject,
    mut v_usedThms_4620_: *mut crate::leanh::LeanObject,
    mut v_approx_4621_: *mut crate::leanh::LeanObject,
    mut v___y_4622_: *mut crate::leanh::LeanObject,
    mut v___y_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
    mut v___y_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_approx_boxed_4632_: u8 = 0;
    let mut v_res_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_approx_boxed_4632_ = (crate::leanh::lean_unbox(v_approx_4621_) as u8);
    v_res_4633_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0(v_goal_4619_, v_usedThms_4620_, v_approx_boxed_4632_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
    crate::leanh::lean_dec(v___y_4630_);
    crate::leanh::lean_dec_ref(v___y_4629_);
    crate::leanh::lean_dec(v___y_4628_);
    crate::leanh::lean_dec_ref(v___y_4627_);
    crate::leanh::lean_dec(v___y_4626_);
    crate::leanh::lean_dec_ref(v___y_4625_);
    crate::leanh::lean_dec(v___y_4624_);
    crate::leanh::lean_dec_ref(v___y_4623_);
    crate::leanh::lean_dec(v___y_4622_);
    crate::leanh::lean_dec_ref(v_usedThms_4620_);
    crate::leanh::lean_dec_ref(v_goal_4619_);
    return v_res_4633_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic(
    mut v_goal_4634_: *mut crate::leanh::LeanObject,
    mut v_usedThms_4635_: *mut crate::leanh::LeanObject,
    mut v_approx_4636_: u8,
    mut v_a_4637_: *mut crate::leanh::LeanObject,
    mut v_a_4638_: *mut crate::leanh::LeanObject,
    mut v_a_4639_: *mut crate::leanh::LeanObject,
    mut v_a_4640_: *mut crate::leanh::LeanObject,
    mut v_a_4641_: *mut crate::leanh::LeanObject,
    mut v_a_4642_: *mut crate::leanh::LeanObject,
    mut v_a_4643_: *mut crate::leanh::LeanObject,
    mut v_a_4644_: *mut crate::leanh::LeanObject,
    mut v_a_4645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mvarId_4647_ = crate::leanh::lean_ctor_get(v_goal_4634_, 1);
    crate::leanh::lean_inc(v_mvarId_4647_);
    v___x_4648_ = crate::leanh::lean_box((v_approx_4636_) as usize);
    v___f_4649_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___lam__0___boxed as *mut core::ffi::c_void, 13, 3);
    crate::leanh::lean_closure_set(v___f_4649_, 0, v_goal_4634_);
    crate::leanh::lean_closure_set(v___f_4649_, 1, v_usedThms_4635_);
    crate::leanh::lean_closure_set(v___f_4649_, 2, v___x_4648_);
    v___x_4650_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___redArg(v_mvarId_4647_, v___f_4649_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
    return v___x_4650_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic___boxed(
    mut v_goal_4651_: *mut crate::leanh::LeanObject,
    mut v_usedThms_4652_: *mut crate::leanh::LeanObject,
    mut v_approx_4653_: *mut crate::leanh::LeanObject,
    mut v_a_4654_: *mut crate::leanh::LeanObject,
    mut v_a_4655_: *mut crate::leanh::LeanObject,
    mut v_a_4656_: *mut crate::leanh::LeanObject,
    mut v_a_4657_: *mut crate::leanh::LeanObject,
    mut v_a_4658_: *mut crate::leanh::LeanObject,
    mut v_a_4659_: *mut crate::leanh::LeanObject,
    mut v_a_4660_: *mut crate::leanh::LeanObject,
    mut v_a_4661_: *mut crate::leanh::LeanObject,
    mut v_a_4662_: *mut crate::leanh::LeanObject,
    mut v_a_4663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_approx_boxed_4664_: u8 = 0;
    let mut v_res_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_approx_boxed_4664_ = (crate::leanh::lean_unbox(v_approx_4653_) as u8);
    v_res_4665_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic(v_goal_4651_, v_usedThms_4652_, v_approx_boxed_4664_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
    crate::leanh::lean_dec(v_a_4662_);
    crate::leanh::lean_dec_ref(v_a_4661_);
    crate::leanh::lean_dec(v_a_4660_);
    crate::leanh::lean_dec_ref(v_a_4659_);
    crate::leanh::lean_dec(v_a_4658_);
    crate::leanh::lean_dec_ref(v_a_4657_);
    crate::leanh::lean_dec(v_a_4656_);
    crate::leanh::lean_dec_ref(v_a_4655_);
    crate::leanh::lean_dec(v_a_4654_);
    return v_res_4665_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0(
    mut v_00_u03b2_4666_: *mut crate::leanh::LeanObject,
    mut v_m_4667_: *mut crate::leanh::LeanObject,
    mut v_a_4668_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4669_: u8 = 0;
    v___x_4669_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0___redArg(v_m_4667_, v_a_4668_);
    return v___x_4669_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0___boxed(
    mut v_00_u03b2_4670_: *mut crate::leanh::LeanObject,
    mut v_m_4671_: *mut crate::leanh::LeanObject,
    mut v_a_4672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4673_: u8 = 0;
    let mut v_r_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4673_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0(v_00_u03b2_4670_, v_m_4671_, v_a_4672_);
    crate::leanh::lean_dec_ref(v_a_4672_);
    crate::leanh::lean_dec_ref(v_m_4671_);
    v_r_4674_ = crate::leanh::lean_box((v_res_4673_) as usize);
    return v_r_4674_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1(
    mut v_00_u03b2_4675_: *mut crate::leanh::LeanObject,
    mut v_m_4676_: *mut crate::leanh::LeanObject,
    mut v_a_4677_: *mut crate::leanh::LeanObject,
    mut v_b_4678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4679_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1___redArg(v_m_4676_, v_a_4677_, v_b_4678_);
    return v___x_4679_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0_spec__0(
    mut v_00_u03b2_4680_: *mut crate::leanh::LeanObject,
    mut v_a_4681_: *mut crate::leanh::LeanObject,
    mut v_x_4682_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4683_: u8 = 0;
    v___x_4683_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0_spec__0___redArg(v_a_4681_, v_x_4682_);
    return v___x_4683_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0_spec__0___boxed(
    mut v_00_u03b2_4684_: *mut crate::leanh::LeanObject,
    mut v_a_4685_: *mut crate::leanh::LeanObject,
    mut v_x_4686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4687_: u8 = 0;
    let mut v_r_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4687_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__0_spec__0(v_00_u03b2_4684_, v_a_4685_, v_x_4686_);
    crate::leanh::lean_dec(v_x_4686_);
    crate::leanh::lean_dec_ref(v_a_4685_);
    v_r_4688_ = crate::leanh::lean_box((v_res_4687_) as usize);
    return v_r_4688_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2(
    mut v_00_u03b2_4689_: *mut crate::leanh::LeanObject,
    mut v_data_4690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4691_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2___redArg(v_data_4690_);
    return v___x_4691_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4692_: *mut crate::leanh::LeanObject,
    mut v_i_4693_: *mut crate::leanh::LeanObject,
    mut v_source_4694_: *mut crate::leanh::LeanObject,
    mut v_target_4695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4696_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2_spec__4___redArg(v_i_4693_, v_source_4694_, v_target_4695_);
    return v___x_4696_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b2_4697_: *mut crate::leanh::LeanObject,
    mut v_x_4698_: *mut crate::leanh::LeanObject,
    mut v_x_4699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4700_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__1_spec__2_spec__4_spec__6___redArg(v_x_4698_, v_x_4699_);
    return v___x_4700_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkNewSeq(
    mut v_goal_4701_: *mut crate::leanh::LeanObject,
    mut v_thms_4702_: *mut crate::leanh::LeanObject,
    mut v_seq_4703_: *mut crate::leanh::LeanObject,
    mut v_approx_4704_: u8,
    mut v_a_4705_: *mut crate::leanh::LeanObject,
    mut v_a_4706_: *mut crate::leanh::LeanObject,
    mut v_a_4707_: *mut crate::leanh::LeanObject,
    mut v_a_4708_: *mut crate::leanh::LeanObject,
    mut v_a_4709_: *mut crate::leanh::LeanObject,
    mut v_a_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
    mut v_a_4713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4720_: u8 = 0;
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4725_: u8 = 0;
    let mut v_a_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4729_: u8 = 0;
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4733_: u8 = 0;
    let mut v___y_4735_: u8 = 0;
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4737_ = lean_array_get_size(v_thms_4702_);
                v___x_4738_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4739_ = lean_nat_dec_eq(v___x_4737_, v___x_4738_);
                if v___x_4739_ == 0 {
                    v___y_4735_ = v___x_4739_;
                    state = 6;
                    continue;
                } else {
                    if v_approx_4704_ == 0 {
                        v___y_4735_ = v___x_4739_;
                        state = 6;
                        continue;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4716_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic(v_goal_4701_, v_thms_4702_, v_approx_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_, v_a_4712_, v_a_4713_);
                if crate::leanh::lean_obj_tag(v___x_4716_) == 0 {
                    v_a_4717_ = crate::leanh::lean_ctor_get(v___x_4716_, 0);
                    v_isSharedCheck_4725_ = (!crate::leanh::lean_is_exclusive(v___x_4716_)) as u8;
                    if v_isSharedCheck_4725_ == 0 {
                        v___x_4719_ = v___x_4716_;
                        v_isShared_4720_ = v_isSharedCheck_4725_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4717_);
                        crate::leanh::lean_dec(v___x_4716_);
                        v___x_4719_ = crate::leanh::lean_box(0);
                        v_isShared_4720_ = v_isSharedCheck_4725_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_seq_4703_);
                    v_a_4726_ = crate::leanh::lean_ctor_get(v___x_4716_, 0);
                    v_isSharedCheck_4733_ = (!crate::leanh::lean_is_exclusive(v___x_4716_)) as u8;
                    if v_isSharedCheck_4733_ == 0 {
                        v___x_4728_ = v___x_4716_;
                        v_isShared_4729_ = v_isSharedCheck_4733_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4726_);
                        crate::leanh::lean_dec(v___x_4716_);
                        v___x_4728_ = crate::leanh::lean_box(0);
                        v_isShared_4729_ = v_isSharedCheck_4733_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4721_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4721_, 0, v_a_4717_);
                crate::leanh::lean_ctor_set(v___x_4721_, 1, v_seq_4703_);
                if v_isShared_4720_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4719_, 0, v___x_4721_);
                    v___x_4723_ = v___x_4719_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4724_, 0, v___x_4721_);
                    v___x_4723_ = v_reuseFailAlloc_4724_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4723_;
            }
            4 => {
                if v_isShared_4729_ == 0 {
                    v___x_4731_ = v___x_4728_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4726_);
                    v___x_4731_ = v_reuseFailAlloc_4732_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4731_;
            }
            6 => {
                if v___y_4735_ == 0 {
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_thms_4702_);
                    crate::leanh::lean_dec_ref(v_goal_4701_);
                    v___x_4736_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4736_, 0, v_seq_4703_);
                    return v___x_4736_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkNewSeq___boxed(
    mut v_goal_4740_: *mut crate::leanh::LeanObject,
    mut v_thms_4741_: *mut crate::leanh::LeanObject,
    mut v_seq_4742_: *mut crate::leanh::LeanObject,
    mut v_approx_4743_: *mut crate::leanh::LeanObject,
    mut v_a_4744_: *mut crate::leanh::LeanObject,
    mut v_a_4745_: *mut crate::leanh::LeanObject,
    mut v_a_4746_: *mut crate::leanh::LeanObject,
    mut v_a_4747_: *mut crate::leanh::LeanObject,
    mut v_a_4748_: *mut crate::leanh::LeanObject,
    mut v_a_4749_: *mut crate::leanh::LeanObject,
    mut v_a_4750_: *mut crate::leanh::LeanObject,
    mut v_a_4751_: *mut crate::leanh::LeanObject,
    mut v_a_4752_: *mut crate::leanh::LeanObject,
    mut v_a_4753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_approx_boxed_4754_: u8 = 0;
    let mut v_res_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_approx_boxed_4754_ = (crate::leanh::lean_unbox(v_approx_4743_) as u8);
    v_res_4755_ =
        l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkNewSeq(
            v_goal_4740_,
            v_thms_4741_,
            v_seq_4742_,
            v_approx_boxed_4754_,
            v_a_4744_,
            v_a_4745_,
            v_a_4746_,
            v_a_4747_,
            v_a_4748_,
            v_a_4749_,
            v_a_4750_,
            v_a_4751_,
            v_a_4752_,
        );
    crate::leanh::lean_dec(v_a_4752_);
    crate::leanh::lean_dec_ref(v_a_4751_);
    crate::leanh::lean_dec(v_a_4750_);
    crate::leanh::lean_dec_ref(v_a_4749_);
    crate::leanh::lean_dec(v_a_4748_);
    crate::leanh::lean_dec_ref(v_a_4747_);
    crate::leanh::lean_dec(v_a_4746_);
    crate::leanh::lean_dec_ref(v_a_4745_);
    crate::leanh::lean_dec(v_a_4744_);
    return v_res_4755_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0_spec__0___redArg(
    mut v_a_4756_: *mut crate::leanh::LeanObject,
    mut v_x_4757_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4758_: u8 = 0;
    let mut v_key_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4757_) == 0 {
                    v___x_4758_ = 0;
                    return v___x_4758_;
                } else {
                    v_key_4759_ = crate::leanh::lean_ctor_get(v_x_4757_, 0);
                    v_tail_4760_ = crate::leanh::lean_ctor_get(v_x_4757_, 2);
                    v___x_4761_ = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(v_key_4759_, v_a_4756_);
                    if v___x_4761_ == 0 {
                        v_x_4757_ = v_tail_4760_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4761_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0_spec__0___redArg___boxed(
    mut v_a_4763_: *mut crate::leanh::LeanObject,
    mut v_x_4764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4765_: u8 = 0;
    let mut v_r_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4765_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0_spec__0___redArg(v_a_4763_, v_x_4764_);
    crate::leanh::lean_dec(v_x_4764_);
    crate::leanh::lean_dec_ref(v_a_4763_);
    v_r_4766_ = crate::leanh::lean_box((v_res_4765_) as usize);
    return v_r_4766_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0___redArg(
    mut v_m_4767_: *mut crate::leanh::LeanObject,
    mut v_a_4768_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: u64 = 0;
    let mut v___x_4772_: u64 = 0;
    let mut v___x_4773_: u64 = 0;
    let mut v_fold_4774_: u64 = 0;
    let mut v___x_4775_: u64 = 0;
    let mut v___x_4776_: u64 = 0;
    let mut v___x_4777_: u64 = 0;
    let mut v___x_4778_: usize = 0;
    let mut v___x_4779_: usize = 0;
    let mut v___x_4780_: usize = 0;
    let mut v___x_4781_: usize = 0;
    let mut v___x_4782_: usize = 0;
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: u8 = 0;
    v_buckets_4769_ = crate::leanh::lean_ctor_get(v_m_4767_, 1);
    v___x_4770_ = lean_array_get_size(v_buckets_4769_);
    v___x_4771_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(v_a_4768_);
    v___x_4772_ = 32u64;
    v___x_4773_ = lean_uint64_shift_right(v___x_4771_, v___x_4772_);
    v_fold_4774_ = lean_uint64_xor(v___x_4771_, v___x_4773_);
    v___x_4775_ = 16u64;
    v___x_4776_ = lean_uint64_shift_right(v_fold_4774_, v___x_4775_);
    v___x_4777_ = lean_uint64_xor(v_fold_4774_, v___x_4776_);
    v___x_4778_ = lean_uint64_to_usize(v___x_4777_);
    v___x_4779_ = lean_usize_of_nat(v___x_4770_);
    v___x_4780_ = 1usize;
    v___x_4781_ = lean_usize_sub(v___x_4779_, v___x_4780_);
    v___x_4782_ = lean_usize_land(v___x_4778_, v___x_4781_);
    v___x_4783_ = lean_array_uget_borrowed(v_buckets_4769_, v___x_4782_);
    v___x_4784_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0_spec__0___redArg(v_a_4768_, v___x_4783_);
    return v___x_4784_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0___redArg___boxed(
    mut v_m_4785_: *mut crate::leanh::LeanObject,
    mut v_a_4786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4787_: u8 = 0;
    let mut v_r_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4787_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0___redArg(v_m_4785_, v_a_4786_);
    crate::leanh::lean_dec_ref(v_a_4786_);
    crate::leanh::lean_dec_ref(v_m_4785_);
    v_r_4788_ = crate::leanh::lean_box((v_res_4787_) as usize);
    return v_r_4788_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2_spec__3_spec__8___redArg(
    mut v_x_4789_: *mut crate::leanh::LeanObject,
    mut v_x_4790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: u64 = 0;
    let mut v___x_4799_: u64 = 0;
    let mut v___x_4800_: u64 = 0;
    let mut v_fold_4801_: u64 = 0;
    let mut v___x_4802_: u64 = 0;
    let mut v___x_4803_: u64 = 0;
    let mut v___x_4804_: u64 = 0;
    let mut v___x_4805_: usize = 0;
    let mut v___x_4806_: usize = 0;
    let mut v___x_4807_: usize = 0;
    let mut v___x_4808_: usize = 0;
    let mut v___x_4809_: usize = 0;
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4790_) == 0 {
                    return v_x_4789_;
                } else {
                    v_key_4791_ = crate::leanh::lean_ctor_get(v_x_4790_, 0);
                    v_value_4792_ = crate::leanh::lean_ctor_get(v_x_4790_, 1);
                    v_tail_4793_ = crate::leanh::lean_ctor_get(v_x_4790_, 2);
                    v_isSharedCheck_4816_ = (!crate::leanh::lean_is_exclusive(v_x_4790_)) as u8;
                    if v_isSharedCheck_4816_ == 0 {
                        v___x_4795_ = v_x_4790_;
                        v_isShared_4796_ = v_isSharedCheck_4816_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4793_);
                        crate::leanh::lean_inc(v_value_4792_);
                        crate::leanh::lean_inc(v_key_4791_);
                        crate::leanh::lean_dec(v_x_4790_);
                        v___x_4795_ = crate::leanh::lean_box(0);
                        v_isShared_4796_ = v_isSharedCheck_4816_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4797_ = lean_array_get_size(v_x_4789_);
                v___x_4798_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(v_key_4791_);
                v___x_4799_ = 32u64;
                v___x_4800_ = lean_uint64_shift_right(v___x_4798_, v___x_4799_);
                v_fold_4801_ = lean_uint64_xor(v___x_4798_, v___x_4800_);
                v___x_4802_ = 16u64;
                v___x_4803_ = lean_uint64_shift_right(v_fold_4801_, v___x_4802_);
                v___x_4804_ = lean_uint64_xor(v_fold_4801_, v___x_4803_);
                v___x_4805_ = lean_uint64_to_usize(v___x_4804_);
                v___x_4806_ = lean_usize_of_nat(v___x_4797_);
                v___x_4807_ = 1usize;
                v___x_4808_ = lean_usize_sub(v___x_4806_, v___x_4807_);
                v___x_4809_ = lean_usize_land(v___x_4805_, v___x_4808_);
                v___x_4810_ = lean_array_uget_borrowed(v_x_4789_, v___x_4809_);
                crate::leanh::lean_inc(v___x_4810_);
                if v_isShared_4796_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4795_, 2, v___x_4810_);
                    v___x_4812_ = v___x_4795_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4815_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4815_, 0, v_key_4791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4815_, 1, v_value_4792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4815_, 2, v___x_4810_);
                    v___x_4812_ = v_reuseFailAlloc_4815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4813_ = lean_array_uset(v_x_4789_, v___x_4809_, v___x_4812_);
                v_x_4789_ = v___x_4813_;
                v_x_4790_ = v_tail_4793_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2_spec__3___redArg(
    mut v_i_4817_: *mut crate::leanh::LeanObject,
    mut v_source_4818_: *mut crate::leanh::LeanObject,
    mut v_target_4819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: u8 = 0;
    let mut v_es_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4820_ = lean_array_get_size(v_source_4818_);
                v___x_4821_ = lean_nat_dec_lt(v_i_4817_, v___x_4820_);
                if v___x_4821_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4818_);
                    crate::leanh::lean_dec(v_i_4817_);
                    return v_target_4819_;
                } else {
                    v_es_4822_ = lean_array_fget(v_source_4818_, v_i_4817_);
                    v___x_4823_ = crate::leanh::lean_box(0);
                    v_source_4824_ = lean_array_fset(v_source_4818_, v_i_4817_, v___x_4823_);
                    v_target_4825_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2_spec__3_spec__8___redArg(v_target_4819_, v_es_4822_);
                    v___x_4826_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4827_ = lean_nat_add(v_i_4817_, v___x_4826_);
                    crate::leanh::lean_dec(v_i_4817_);
                    v_i_4817_ = v___x_4827_;
                    v_source_4818_ = v_source_4824_;
                    v_target_4819_ = v_target_4825_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2___redArg(
    mut v_data_4829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4830_ = lean_array_get_size(v_data_4829_);
    v___x_4831_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4832_ = lean_nat_mul(v___x_4830_, v___x_4831_);
    v___x_4833_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4834_ = crate::leanh::lean_box(0);
    v___x_4835_ = lean_mk_array(v_nbuckets_4832_, v___x_4834_);
    v___x_4836_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2_spec__3___redArg(v___x_4833_, v_data_4829_, v___x_4835_);
    return v___x_4836_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__3___redArg(
    mut v_a_4837_: *mut crate::leanh::LeanObject,
    mut v_b_4838_: *mut crate::leanh::LeanObject,
    mut v_x_4839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4845_: u8 = 0;
    let mut v___x_4846_: u8 = 0;
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4854_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4839_) == 0 {
                    crate::leanh::lean_dec(v_b_4838_);
                    crate::leanh::lean_dec_ref(v_a_4837_);
                    return v_x_4839_;
                } else {
                    v_key_4840_ = crate::leanh::lean_ctor_get(v_x_4839_, 0);
                    v_value_4841_ = crate::leanh::lean_ctor_get(v_x_4839_, 1);
                    v_tail_4842_ = crate::leanh::lean_ctor_get(v_x_4839_, 2);
                    v_isSharedCheck_4854_ = (!crate::leanh::lean_is_exclusive(v_x_4839_)) as u8;
                    if v_isSharedCheck_4854_ == 0 {
                        v___x_4844_ = v_x_4839_;
                        v_isShared_4845_ = v_isSharedCheck_4854_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4842_);
                        crate::leanh::lean_inc(v_value_4841_);
                        crate::leanh::lean_inc(v_key_4840_);
                        crate::leanh::lean_dec(v_x_4839_);
                        v___x_4844_ = crate::leanh::lean_box(0);
                        v_isShared_4845_ = v_isSharedCheck_4854_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4846_ = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(v_key_4840_, v_a_4837_);
                if v___x_4846_ == 0 {
                    v___x_4847_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__3___redArg(v_a_4837_, v_b_4838_, v_tail_4842_);
                    if v_isShared_4845_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4844_, 2, v___x_4847_);
                        v___x_4849_ = v___x_4844_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4850_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_key_4840_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_value_4841_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 2, v___x_4847_);
                        v___x_4849_ = v_reuseFailAlloc_4850_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4841_);
                    crate::leanh::lean_dec(v_key_4840_);
                    if v_isShared_4845_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4844_, 1, v_b_4838_);
                        crate::leanh::lean_ctor_set(v___x_4844_, 0, v_a_4837_);
                        v___x_4852_ = v___x_4844_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4853_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4837_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4853_, 1, v_b_4838_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4853_, 2, v_tail_4842_);
                        v___x_4852_ = v_reuseFailAlloc_4853_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4849_;
            }
            3 => {
                return v___x_4852_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1___redArg(
    mut v_m_4855_: *mut crate::leanh::LeanObject,
    mut v_a_4856_: *mut crate::leanh::LeanObject,
    mut v_b_4857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4862_: u8 = 0;
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: u64 = 0;
    let mut v___x_4865_: u64 = 0;
    let mut v___x_4866_: u64 = 0;
    let mut v_fold_4867_: u64 = 0;
    let mut v___x_4868_: u64 = 0;
    let mut v___x_4869_: u64 = 0;
    let mut v___x_4870_: u64 = 0;
    let mut v___x_4871_: usize = 0;
    let mut v___x_4872_: usize = 0;
    let mut v___x_4873_: usize = 0;
    let mut v___x_4874_: usize = 0;
    let mut v___x_4875_: usize = 0;
    let mut v_bkt_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: u8 = 0;
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: u8 = 0;
    let mut v_val_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4858_ = crate::leanh::lean_ctor_get(v_m_4855_, 0);
                v_buckets_4859_ = crate::leanh::lean_ctor_get(v_m_4855_, 1);
                v_isSharedCheck_4902_ = (!crate::leanh::lean_is_exclusive(v_m_4855_)) as u8;
                if v_isSharedCheck_4902_ == 0 {
                    v___x_4861_ = v_m_4855_;
                    v_isShared_4862_ = v_isSharedCheck_4902_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4859_);
                    crate::leanh::lean_inc(v_size_4858_);
                    crate::leanh::lean_dec(v_m_4855_);
                    v___x_4861_ = crate::leanh::lean_box(0);
                    v_isShared_4862_ = v_isSharedCheck_4902_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4863_ = lean_array_get_size(v_buckets_4859_);
                v___x_4864_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(v_a_4856_);
                v___x_4865_ = 32u64;
                v___x_4866_ = lean_uint64_shift_right(v___x_4864_, v___x_4865_);
                v_fold_4867_ = lean_uint64_xor(v___x_4864_, v___x_4866_);
                v___x_4868_ = 16u64;
                v___x_4869_ = lean_uint64_shift_right(v_fold_4867_, v___x_4868_);
                v___x_4870_ = lean_uint64_xor(v_fold_4867_, v___x_4869_);
                v___x_4871_ = lean_uint64_to_usize(v___x_4870_);
                v___x_4872_ = lean_usize_of_nat(v___x_4863_);
                v___x_4873_ = 1usize;
                v___x_4874_ = lean_usize_sub(v___x_4872_, v___x_4873_);
                v___x_4875_ = lean_usize_land(v___x_4871_, v___x_4874_);
                v_bkt_4876_ = lean_array_uget_borrowed(v_buckets_4859_, v___x_4875_);
                v___x_4877_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0_spec__0___redArg(v_a_4856_, v_bkt_4876_);
                if v___x_4877_ == 0 {
                    v___x_4878_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4879_ = lean_nat_add(v_size_4858_, v___x_4878_);
                    crate::leanh::lean_dec(v_size_4858_);
                    crate::leanh::lean_inc(v_bkt_4876_);
                    v___x_4880_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4880_, 0, v_a_4856_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 1, v_b_4857_);
                    crate::leanh::lean_ctor_set(v___x_4880_, 2, v_bkt_4876_);
                    v_buckets_x27_4881_ =
                        lean_array_uset(v_buckets_4859_, v___x_4875_, v___x_4880_);
                    v___x_4882_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4883_ = lean_nat_mul(v_size_x27_4879_, v___x_4882_);
                    v___x_4884_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4885_ = lean_nat_div(v___x_4883_, v___x_4884_);
                    crate::leanh::lean_dec(v___x_4883_);
                    v___x_4886_ = lean_array_get_size(v_buckets_x27_4881_);
                    v___x_4887_ = lean_nat_dec_le(v___x_4885_, v___x_4886_);
                    crate::leanh::lean_dec(v___x_4885_);
                    if v___x_4887_ == 0 {
                        v_val_4888_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2___redArg(v_buckets_x27_4881_);
                        if v_isShared_4862_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4861_, 1, v_val_4888_);
                            crate::leanh::lean_ctor_set(v___x_4861_, 0, v_size_x27_4879_);
                            v___x_4890_ = v___x_4861_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4891_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4891_,
                                0,
                                v_size_x27_4879_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4891_, 1, v_val_4888_);
                            v___x_4890_ = v_reuseFailAlloc_4891_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4862_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4861_, 1, v_buckets_x27_4881_);
                            crate::leanh::lean_ctor_set(v___x_4861_, 0, v_size_x27_4879_);
                            v___x_4893_ = v___x_4861_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4894_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4894_,
                                0,
                                v_size_x27_4879_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4894_,
                                1,
                                v_buckets_x27_4881_,
                            );
                            v___x_4893_ = v_reuseFailAlloc_4894_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4876_);
                    v___x_4895_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4896_ =
                        lean_array_uset(v_buckets_4859_, v___x_4875_, v___x_4895_);
                    v___x_4897_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__3___redArg(v_a_4856_, v_b_4857_, v_bkt_4876_);
                    v___x_4898_ = lean_array_uset(v_buckets_x27_4896_, v___x_4875_, v___x_4897_);
                    if v_isShared_4862_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4861_, 1, v___x_4898_);
                        v___x_4900_ = v___x_4861_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4901_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_size_4858_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4901_, 1, v___x_4898_);
                        v___x_4900_ = v_reuseFailAlloc_4901_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4890_;
            }
            3 => {
                return v___x_4893_;
            }
            4 => {
                return v___x_4900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__2(
    mut v_as_4903_: *mut crate::leanh::LeanObject,
    mut v_sz_4904_: usize,
    mut v_i_4905_: usize,
    mut v_b_4906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: usize = 0;
    let mut v___x_4910_: usize = 0;
    let mut v___x_4912_: u8 = 0;
    let mut v_a_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4919_: u8 = 0;
    let mut v___x_4920_: u8 = 0;
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4912_ = lean_usize_dec_lt(v_i_4905_, v_sz_4904_);
                if v___x_4912_ == 0 {
                    return v_b_4906_;
                } else {
                    v_a_4913_ = lean_array_uget_borrowed(v_as_4903_, v_i_4905_);
                    v_snd_4914_ = crate::leanh::lean_ctor_get(v_a_4913_, 1);
                    v_fst_4915_ = crate::leanh::lean_ctor_get(v_b_4906_, 0);
                    v_snd_4916_ = crate::leanh::lean_ctor_get(v_b_4906_, 1);
                    v_isSharedCheck_4930_ = (!crate::leanh::lean_is_exclusive(v_b_4906_)) as u8;
                    if v_isSharedCheck_4930_ == 0 {
                        v___x_4918_ = v_b_4906_;
                        v_isShared_4919_ = v_isSharedCheck_4930_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4916_);
                        crate::leanh::lean_inc(v_fst_4915_);
                        crate::leanh::lean_dec(v_b_4906_);
                        v___x_4918_ = crate::leanh::lean_box(0);
                        v_isShared_4919_ = v_isSharedCheck_4930_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4909_ = 1usize;
                v___x_4910_ = lean_usize_add(v_i_4905_, v___x_4909_);
                v_i_4905_ = v___x_4910_;
                v_b_4906_ = v_a_4908_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4920_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0___redArg(v_fst_4915_, v_snd_4914_);
                if v___x_4920_ == 0 {
                    v___x_4921_ = lean_array_get_size(v_snd_4916_);
                    crate::leanh::lean_inc_n(v_snd_4914_, 2);
                    v___x_4922_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1___redArg(v_fst_4915_, v_snd_4914_, v___x_4921_);
                    v___x_4923_ = lean_array_push(v_snd_4916_, v_snd_4914_);
                    if v_isShared_4919_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4918_, 1, v___x_4923_);
                        crate::leanh::lean_ctor_set(v___x_4918_, 0, v___x_4922_);
                        v___x_4925_ = v___x_4918_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4926_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4922_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4926_, 1, v___x_4923_);
                        v___x_4925_ = v_reuseFailAlloc_4926_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_4919_ == 0 {
                        v___x_4928_ = v___x_4918_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4929_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_fst_4915_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4929_, 1, v_snd_4916_);
                        v___x_4928_ = v_reuseFailAlloc_4929_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_4908_ = v___x_4925_;
                state = 1;
                continue;
            }
            4 => {
                v_a_4908_ = v___x_4928_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__2___boxed(
    mut v_as_4931_: *mut crate::leanh::LeanObject,
    mut v_sz_4932_: *mut crate::leanh::LeanObject,
    mut v_i_4933_: *mut crate::leanh::LeanObject,
    mut v_b_4934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4935_: usize = 0;
    let mut v_i_boxed_4936_: usize = 0;
    let mut v_res_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4935_ = crate::leanh::lean_unbox_usize(v_sz_4932_);
    crate::leanh::lean_dec(v_sz_4932_);
    v_i_boxed_4936_ = crate::leanh::lean_unbox_usize(v_i_4933_);
    crate::leanh::lean_dec(v_i_4933_);
    v_res_4937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__2(v_as_4931_, v_sz_boxed_4935_, v_i_boxed_4936_, v_b_4934_);
    crate::leanh::lean_dec_ref(v_as_4931_);
    return v_res_4937_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__4(
    mut v_x_4938_: *mut crate::leanh::LeanObject,
    mut v_x_4939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4939_) == 0 {
                    return v_x_4938_;
                } else {
                    v_key_4940_ = crate::leanh::lean_ctor_get(v_x_4939_, 0);
                    v_value_4941_ = crate::leanh::lean_ctor_get(v_x_4939_, 1);
                    v_tail_4942_ = crate::leanh::lean_ctor_get(v_x_4939_, 2);
                    crate::leanh::lean_inc(v_value_4941_);
                    crate::leanh::lean_inc(v_key_4940_);
                    v___x_4943_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4943_, 0, v_key_4940_);
                    crate::leanh::lean_ctor_set(v___x_4943_, 1, v_value_4941_);
                    v___x_4944_ = lean_array_push(v_x_4938_, v___x_4943_);
                    v_x_4938_ = v___x_4944_;
                    v_x_4939_ = v_tail_4942_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__4___boxed(
    mut v_x_4946_: *mut crate::leanh::LeanObject,
    mut v_x_4947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4948_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__4(v_x_4946_, v_x_4947_);
    crate::leanh::lean_dec(v_x_4947_);
    return v_res_4948_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__5(
    mut v_as_4949_: *mut crate::leanh::LeanObject,
    mut v_i_4950_: usize,
    mut v_stop_4951_: usize,
    mut v_b_4952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4953_: u8 = 0;
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: usize = 0;
    let mut v___x_4957_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4953_ = lean_usize_dec_eq(v_i_4950_, v_stop_4951_);
                if v___x_4953_ == 0 {
                    v___x_4954_ = lean_array_uget_borrowed(v_as_4949_, v_i_4950_);
                    v___x_4955_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__4(v_b_4952_, v___x_4954_);
                    v___x_4956_ = 1usize;
                    v___x_4957_ = lean_usize_add(v_i_4950_, v___x_4956_);
                    v_i_4950_ = v___x_4957_;
                    v_b_4952_ = v___x_4955_;
                    state = 0;
                    continue;
                } else {
                    return v_b_4952_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__5___boxed(
    mut v_as_4959_: *mut crate::leanh::LeanObject,
    mut v_i_4960_: *mut crate::leanh::LeanObject,
    mut v_stop_4961_: *mut crate::leanh::LeanObject,
    mut v_b_4962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4963_: usize = 0;
    let mut v_stop_boxed_4964_: usize = 0;
    let mut v_res_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4963_ = crate::leanh::lean_unbox_usize(v_i_4960_);
    crate::leanh::lean_dec(v_i_4960_);
    v_stop_boxed_4964_ = crate::leanh::lean_unbox_usize(v_stop_4961_);
    crate::leanh::lean_dec(v_stop_4961_);
    v_res_4965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__5(v_as_4959_, v_i_boxed_4963_, v_stop_boxed_4964_, v_b_4962_);
    crate::leanh::lean_dec_ref(v_as_4959_);
    return v_res_4965_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg___lam__0(
    mut v_x_4966_: *mut crate::leanh::LeanObject,
    mut v_x_4967_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: u8 = 0;
    v_fst_4968_ = crate::leanh::lean_ctor_get(v_x_4966_, 0);
    v_fst_4969_ = crate::leanh::lean_ctor_get(v_x_4967_, 0);
    v___x_4970_ = l_Lean_Name_lt(v_fst_4968_, v_fst_4969_);
    return v___x_4970_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg___lam__0___boxed(
    mut v_x_4971_: *mut crate::leanh::LeanObject,
    mut v_x_4972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4973_: u8 = 0;
    let mut v_r_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4973_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg___lam__0(v_x_4971_, v_x_4972_);
    crate::leanh::lean_dec_ref(v_x_4972_);
    crate::leanh::lean_dec_ref(v_x_4971_);
    v_r_4974_ = crate::leanh::lean_box((v_res_4973_) as usize);
    return v_r_4974_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3_spec__6___redArg(
    mut v_hi_4975_: *mut crate::leanh::LeanObject,
    mut v_pivot_4976_: *mut crate::leanh::LeanObject,
    mut v_as_4977_: *mut crate::leanh::LeanObject,
    mut v_i_4978_: *mut crate::leanh::LeanObject,
    mut v_k_4979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4980_: u8 = 0;
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: u8 = 0;
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4980_ = lean_nat_dec_lt(v_k_4979_, v_hi_4975_);
                if v___x_4980_ == 0 {
                    crate::leanh::lean_dec(v_k_4979_);
                    v___x_4981_ = lean_array_fswap(v_as_4977_, v_i_4978_, v_hi_4975_);
                    v___x_4982_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4982_, 0, v_i_4978_);
                    crate::leanh::lean_ctor_set(v___x_4982_, 1, v___x_4981_);
                    return v___x_4982_;
                } else {
                    v___x_4983_ = lean_array_fget_borrowed(v_as_4977_, v_k_4979_);
                    v_fst_4984_ = crate::leanh::lean_ctor_get(v___x_4983_, 0);
                    v_fst_4985_ = crate::leanh::lean_ctor_get(v_pivot_4976_, 0);
                    v___x_4986_ = l_Lean_Name_lt(v_fst_4984_, v_fst_4985_);
                    if v___x_4986_ == 0 {
                        v___x_4987_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4988_ = lean_nat_add(v_k_4979_, v___x_4987_);
                        crate::leanh::lean_dec(v_k_4979_);
                        v_k_4979_ = v___x_4988_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4990_ = lean_array_fswap(v_as_4977_, v_i_4978_, v_k_4979_);
                        v___x_4991_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4992_ = lean_nat_add(v_i_4978_, v___x_4991_);
                        crate::leanh::lean_dec(v_i_4978_);
                        v___x_4993_ = lean_nat_add(v_k_4979_, v___x_4991_);
                        crate::leanh::lean_dec(v_k_4979_);
                        v_as_4977_ = v___x_4990_;
                        v_i_4978_ = v___x_4992_;
                        v_k_4979_ = v___x_4993_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3_spec__6___redArg___boxed(
    mut v_hi_4995_: *mut crate::leanh::LeanObject,
    mut v_pivot_4996_: *mut crate::leanh::LeanObject,
    mut v_as_4997_: *mut crate::leanh::LeanObject,
    mut v_i_4998_: *mut crate::leanh::LeanObject,
    mut v_k_4999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5000_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3_spec__6___redArg(v_hi_4995_, v_pivot_4996_, v_as_4997_, v_i_4998_, v_k_4999_);
    crate::leanh::lean_dec_ref(v_pivot_4996_);
    crate::leanh::lean_dec(v_hi_4995_);
    return v_res_5000_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg(
    mut v_n_5001_: *mut crate::leanh::LeanObject,
    mut v_as_5002_: *mut crate::leanh::LeanObject,
    mut v_lo_5003_: *mut crate::leanh::LeanObject,
    mut v_hi_5004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: u8 = 0;
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: u8 = 0;
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: u8 = 0;
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: u8 = 0;
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5016_ = lean_nat_dec_lt(v_lo_5003_, v_hi_5004_);
                if v___x_5016_ == 0 {
                    crate::leanh::lean_dec(v_lo_5003_);
                    return v_as_5002_;
                } else {
                    v___x_5017_ = lean_nat_add(v_lo_5003_, v_hi_5004_);
                    v___x_5018_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_5019_ = lean_nat_shiftr(v___x_5017_, v___x_5018_);
                    crate::leanh::lean_dec(v___x_5017_);
                    v___x_5032_ = lean_array_fget_borrowed(v_as_5002_, v_mid_5019_);
                    v___x_5033_ = lean_array_fget_borrowed(v_as_5002_, v_lo_5003_);
                    v___x_5034_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg___lam__0(v___x_5032_, v___x_5033_);
                    if v___x_5034_ == 0 {
                        v___y_5027_ = v_as_5002_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5035_ = lean_array_fswap(v_as_5002_, v_lo_5003_, v_mid_5019_);
                        v___y_5027_ = v___x_5035_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_5007_ = lean_array_fget(v___y_5006_, v_hi_5004_);
                crate::leanh::lean_inc_n(v_lo_5003_, 2);
                v___x_5008_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3_spec__6___redArg(v_hi_5004_, v_pivot_5007_, v___y_5006_, v_lo_5003_, v_lo_5003_);
                crate::leanh::lean_dec(v_pivot_5007_);
                v_fst_5009_ = crate::leanh::lean_ctor_get(v___x_5008_, 0);
                crate::leanh::lean_inc(v_fst_5009_);
                v_snd_5010_ = crate::leanh::lean_ctor_get(v___x_5008_, 1);
                crate::leanh::lean_inc(v_snd_5010_);
                crate::leanh::lean_dec_ref(v___x_5008_);
                v___x_5011_ = lean_nat_dec_le(v_hi_5004_, v_fst_5009_);
                if v___x_5011_ == 0 {
                    v___x_5012_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg(v_n_5001_, v_snd_5010_, v_lo_5003_, v_fst_5009_);
                    v___x_5013_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5014_ = lean_nat_add(v_fst_5009_, v___x_5013_);
                    crate::leanh::lean_dec(v_fst_5009_);
                    v_as_5002_ = v___x_5012_;
                    v_lo_5003_ = v___x_5014_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_5009_);
                    crate::leanh::lean_dec(v_lo_5003_);
                    return v_snd_5010_;
                }
            }
            2 => {
                v___x_5022_ = lean_array_fget_borrowed(v___y_5021_, v_mid_5019_);
                v___x_5023_ = lean_array_fget_borrowed(v___y_5021_, v_hi_5004_);
                v___x_5024_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg___lam__0(v___x_5022_, v___x_5023_);
                if v___x_5024_ == 0 {
                    crate::leanh::lean_dec(v_mid_5019_);
                    v___y_5006_ = v___y_5021_;
                    state = 1;
                    continue;
                } else {
                    v___x_5025_ = lean_array_fswap(v___y_5021_, v_mid_5019_, v_hi_5004_);
                    crate::leanh::lean_dec(v_mid_5019_);
                    v___y_5006_ = v___x_5025_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5028_ = lean_array_fget_borrowed(v___y_5027_, v_hi_5004_);
                v___x_5029_ = lean_array_fget_borrowed(v___y_5027_, v_lo_5003_);
                v___x_5030_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg___lam__0(v___x_5028_, v___x_5029_);
                if v___x_5030_ == 0 {
                    v___y_5021_ = v___y_5027_;
                    state = 2;
                    continue;
                } else {
                    v___x_5031_ = lean_array_fswap(v___y_5027_, v_lo_5003_, v_hi_5004_);
                    v___y_5021_ = v___x_5031_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg___boxed(
    mut v_n_5036_: *mut crate::leanh::LeanObject,
    mut v_as_5037_: *mut crate::leanh::LeanObject,
    mut v_lo_5038_: *mut crate::leanh::LeanObject,
    mut v_hi_5039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5040_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg(v_n_5036_, v_as_5037_, v_lo_5038_, v_hi_5039_);
    crate::leanh::lean_dec(v_hi_5039_);
    crate::leanh::lean_dec(v_n_5036_);
    return v_res_5040_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5041_ = crate::leanh::lean_box(0);
    v___x_5042_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5043_ = lean_mk_array(v___x_5042_, v___x_5041_);
    return v___x_5043_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5044_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__0);
    v___x_5045_ = crate::leanh::lean_unsigned_to_nat(0);
    v_map_5046_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_map_5046_, 0, v___x_5045_);
    crate::leanh::lean_ctor_set(v_map_5046_, 1, v___x_5044_);
    return v_map_5046_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v_thms_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_thms_5047_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__2;
    v_map_5048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__1);
    v___x_5049_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5049_, 0, v_map_5048_);
    crate::leanh::lean_ctor_set(v___x_5049_, 1, v_thms_5047_);
    return v___x_5049_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems(
    mut v_map_5050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5054_: usize = 0;
    let mut v___x_5055_: usize = 0;
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5061_: u8 = 0;
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5065_: u8 = 0;
    let mut v___y_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: u8 = 0;
    let mut v___y_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: u8 = 0;
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: u8 = 0;
    let mut v_size_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: u8 = 0;
    let mut v___x_5092_: u8 = 0;
    let mut v___x_5093_: usize = 0;
    let mut v___x_5094_: usize = 0;
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: usize = 0;
    let mut v___x_5097_: usize = 0;
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5086_ = crate::leanh::lean_ctor_get(v_map_5050_, 0);
                v_buckets_5087_ = crate::leanh::lean_ctor_get(v_map_5050_, 1);
                v___x_5088_ = lean_mk_empty_array_with_capacity(v_size_5086_);
                v___x_5089_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5090_ = lean_array_get_size(v_buckets_5087_);
                v___x_5091_ = lean_nat_dec_lt(v___x_5089_, v___x_5090_);
                if v___x_5091_ == 0 {
                    v___y_5079_ = v___x_5088_;
                    state = 6;
                    continue;
                } else {
                    v___x_5092_ = lean_nat_dec_le(v___x_5090_, v___x_5090_);
                    if v___x_5092_ == 0 {
                        if v___x_5091_ == 0 {
                            v___y_5079_ = v___x_5088_;
                            state = 6;
                            continue;
                        } else {
                            v___x_5093_ = 0usize;
                            v___x_5094_ = lean_usize_of_nat(v___x_5090_);
                            v___x_5095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__5(v_buckets_5087_, v___x_5093_, v___x_5094_, v___x_5088_);
                            v___y_5079_ = v___x_5095_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_5096_ = 0usize;
                        v___x_5097_ = lean_usize_of_nat(v___x_5090_);
                        v___x_5098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__5(v_buckets_5087_, v___x_5096_, v___x_5097_, v___x_5088_);
                        v___y_5079_ = v___x_5098_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5053_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___closed__2);
                v_sz_5054_ = lean_array_size(v___y_5052_);
                v___x_5055_ = 0usize;
                v___x_5056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__2(v___y_5052_, v_sz_5054_, v___x_5055_, v___x_5053_);
                crate::leanh::lean_dec_ref(v___y_5052_);
                v_fst_5057_ = crate::leanh::lean_ctor_get(v___x_5056_, 0);
                v_snd_5058_ = crate::leanh::lean_ctor_get(v___x_5056_, 1);
                v_isSharedCheck_5065_ = (!crate::leanh::lean_is_exclusive(v___x_5056_)) as u8;
                if v_isSharedCheck_5065_ == 0 {
                    v___x_5060_ = v___x_5056_;
                    v_isShared_5061_ = v_isSharedCheck_5065_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5058_);
                    crate::leanh::lean_inc(v_fst_5057_);
                    crate::leanh::lean_dec(v___x_5056_);
                    v___x_5060_ = crate::leanh::lean_box(0);
                    v_isShared_5061_ = v_isSharedCheck_5065_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5061_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5060_, 1, v_fst_5057_);
                    crate::leanh::lean_ctor_set(v___x_5060_, 0, v_snd_5058_);
                    v___x_5063_ = v___x_5060_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5064_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_snd_5058_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5064_, 1, v_fst_5057_);
                    v___x_5063_ = v_reuseFailAlloc_5064_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5063_;
            }
            4 => {
                v___x_5071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg(v___y_5069_, v___y_5067_, v___y_5068_, v___y_5070_);
                crate::leanh::lean_dec(v___y_5070_);
                crate::leanh::lean_dec(v___y_5069_);
                v___y_5052_ = v___x_5071_;
                state = 1;
                continue;
            }
            5 => {
                v___x_5077_ = lean_nat_dec_le(v___y_5076_, v___y_5075_);
                if v___x_5077_ == 0 {
                    crate::leanh::lean_dec(v___y_5075_);
                    crate::leanh::lean_inc(v___y_5076_);
                    v___y_5067_ = v___y_5073_;
                    v___y_5068_ = v___y_5076_;
                    v___y_5069_ = v___y_5074_;
                    v___y_5070_ = v___y_5076_;
                    state = 4;
                    continue;
                } else {
                    v___y_5067_ = v___y_5073_;
                    v___y_5068_ = v___y_5076_;
                    v___y_5069_ = v___y_5074_;
                    v___y_5070_ = v___y_5075_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_5080_ = lean_array_get_size(v___y_5079_);
                v___x_5081_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5082_ = lean_nat_dec_eq(v___x_5080_, v___x_5081_);
                if v___x_5082_ == 0 {
                    v___x_5083_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5084_ = lean_nat_sub(v___x_5080_, v___x_5083_);
                    v___x_5085_ = lean_nat_dec_le(v___x_5081_, v___x_5084_);
                    if v___x_5085_ == 0 {
                        crate::leanh::lean_inc(v___x_5084_);
                        v___y_5073_ = v___y_5079_;
                        v___y_5074_ = v___x_5080_;
                        v___y_5075_ = v___x_5084_;
                        v___y_5076_ = v___x_5084_;
                        state = 5;
                        continue;
                    } else {
                        v___y_5073_ = v___y_5079_;
                        v___y_5074_ = v___x_5080_;
                        v___y_5075_ = v___x_5084_;
                        v___y_5076_ = v___x_5081_;
                        state = 5;
                        continue;
                    }
                } else {
                    v___y_5052_ = v___y_5079_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems___boxed(
    mut v_map_5099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5100_ =
        l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems(
            v_map_5099_,
        );
    crate::leanh::lean_dec_ref(v_map_5099_);
    return v_res_5100_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0(
    mut v_00_u03b2_5101_: *mut crate::leanh::LeanObject,
    mut v_m_5102_: *mut crate::leanh::LeanObject,
    mut v_a_5103_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5104_: u8 = 0;
    v___x_5104_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0___redArg(v_m_5102_, v_a_5103_);
    return v___x_5104_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0___boxed(
    mut v_00_u03b2_5105_: *mut crate::leanh::LeanObject,
    mut v_m_5106_: *mut crate::leanh::LeanObject,
    mut v_a_5107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5108_: u8 = 0;
    let mut v_r_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5108_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0(v_00_u03b2_5105_, v_m_5106_, v_a_5107_);
    crate::leanh::lean_dec_ref(v_a_5107_);
    crate::leanh::lean_dec_ref(v_m_5106_);
    v_r_5109_ = crate::leanh::lean_box((v_res_5108_) as usize);
    return v_r_5109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1(
    mut v_00_u03b2_5110_: *mut crate::leanh::LeanObject,
    mut v_m_5111_: *mut crate::leanh::LeanObject,
    mut v_a_5112_: *mut crate::leanh::LeanObject,
    mut v_b_5113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5114_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1___redArg(v_m_5111_, v_a_5112_, v_b_5113_);
    return v___x_5114_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3(
    mut v_n_5115_: *mut crate::leanh::LeanObject,
    mut v_as_5116_: *mut crate::leanh::LeanObject,
    mut v_lo_5117_: *mut crate::leanh::LeanObject,
    mut v_hi_5118_: *mut crate::leanh::LeanObject,
    mut v_w_5119_: *mut crate::leanh::LeanObject,
    mut v_hlo_5120_: *mut crate::leanh::LeanObject,
    mut v_hhi_5121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5122_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___redArg(v_n_5115_, v_as_5116_, v_lo_5117_, v_hi_5118_);
    return v___x_5122_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3___boxed(
    mut v_n_5123_: *mut crate::leanh::LeanObject,
    mut v_as_5124_: *mut crate::leanh::LeanObject,
    mut v_lo_5125_: *mut crate::leanh::LeanObject,
    mut v_hi_5126_: *mut crate::leanh::LeanObject,
    mut v_w_5127_: *mut crate::leanh::LeanObject,
    mut v_hlo_5128_: *mut crate::leanh::LeanObject,
    mut v_hhi_5129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3(v_n_5123_, v_as_5124_, v_lo_5125_, v_hi_5126_, v_w_5127_, v_hlo_5128_, v_hhi_5129_);
    crate::leanh::lean_dec(v_hi_5126_);
    crate::leanh::lean_dec(v_n_5123_);
    return v_res_5130_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0_spec__0(
    mut v_00_u03b2_5131_: *mut crate::leanh::LeanObject,
    mut v_a_5132_: *mut crate::leanh::LeanObject,
    mut v_x_5133_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5134_: u8 = 0;
    v___x_5134_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0_spec__0___redArg(v_a_5132_, v_x_5133_);
    return v___x_5134_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0_spec__0___boxed(
    mut v_00_u03b2_5135_: *mut crate::leanh::LeanObject,
    mut v_a_5136_: *mut crate::leanh::LeanObject,
    mut v_x_5137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5138_: u8 = 0;
    let mut v_r_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__0_spec__0(v_00_u03b2_5135_, v_a_5136_, v_x_5137_);
    crate::leanh::lean_dec(v_x_5137_);
    crate::leanh::lean_dec_ref(v_a_5136_);
    v_r_5139_ = crate::leanh::lean_box((v_res_5138_) as usize);
    return v_r_5139_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2(
    mut v_00_u03b2_5140_: *mut crate::leanh::LeanObject,
    mut v_data_5141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2___redArg(v_data_5141_);
    return v___x_5142_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__3(
    mut v_00_u03b2_5143_: *mut crate::leanh::LeanObject,
    mut v_a_5144_: *mut crate::leanh::LeanObject,
    mut v_b_5145_: *mut crate::leanh::LeanObject,
    mut v_x_5146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5147_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__3___redArg(v_a_5144_, v_b_5145_, v_x_5146_);
    return v___x_5147_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3_spec__6(
    mut v_n_5148_: *mut crate::leanh::LeanObject,
    mut v_lo_5149_: *mut crate::leanh::LeanObject,
    mut v_hi_5150_: *mut crate::leanh::LeanObject,
    mut v_hhi_5151_: *mut crate::leanh::LeanObject,
    mut v_pivot_5152_: *mut crate::leanh::LeanObject,
    mut v_as_5153_: *mut crate::leanh::LeanObject,
    mut v_i_5154_: *mut crate::leanh::LeanObject,
    mut v_k_5155_: *mut crate::leanh::LeanObject,
    mut v_ilo_5156_: *mut crate::leanh::LeanObject,
    mut v_ik_5157_: *mut crate::leanh::LeanObject,
    mut v_w_5158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5159_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3_spec__6___redArg(v_hi_5150_, v_pivot_5152_, v_as_5153_, v_i_5154_, v_k_5155_);
    return v___x_5159_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3_spec__6___boxed(
    mut v_n_5160_: *mut crate::leanh::LeanObject,
    mut v_lo_5161_: *mut crate::leanh::LeanObject,
    mut v_hi_5162_: *mut crate::leanh::LeanObject,
    mut v_hhi_5163_: *mut crate::leanh::LeanObject,
    mut v_pivot_5164_: *mut crate::leanh::LeanObject,
    mut v_as_5165_: *mut crate::leanh::LeanObject,
    mut v_i_5166_: *mut crate::leanh::LeanObject,
    mut v_k_5167_: *mut crate::leanh::LeanObject,
    mut v_ilo_5168_: *mut crate::leanh::LeanObject,
    mut v_ik_5169_: *mut crate::leanh::LeanObject,
    mut v_w_5170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5171_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__3_spec__6(v_n_5160_, v_lo_5161_, v_hi_5162_, v_hhi_5163_, v_pivot_5164_, v_as_5165_, v_i_5166_, v_k_5167_, v_ilo_5168_, v_ik_5169_, v_w_5170_);
    crate::leanh::lean_dec_ref(v_pivot_5164_);
    crate::leanh::lean_dec(v_hi_5162_);
    crate::leanh::lean_dec(v_lo_5161_);
    crate::leanh::lean_dec(v_n_5160_);
    return v_res_5171_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2_spec__3(
    mut v_00_u03b2_5172_: *mut crate::leanh::LeanObject,
    mut v_i_5173_: *mut crate::leanh::LeanObject,
    mut v_source_5174_: *mut crate::leanh::LeanObject,
    mut v_target_5175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5176_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2_spec__3___redArg(v_i_5173_, v_source_5174_, v_target_5175_);
    return v___x_5176_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2_spec__3_spec__8(
    mut v_00_u03b2_5177_: *mut crate::leanh::LeanObject,
    mut v_x_5178_: *mut crate::leanh::LeanObject,
    mut v_x_5179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5180_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems_spec__1_spec__2_spec__3_spec__8___redArg(v_x_5178_, v_x_5179_);
    return v___x_5180_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0_spec__0___redArg(
    mut v_a_5181_: *mut crate::leanh::LeanObject,
    mut v_x_5182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: u8 = 0;
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5182_) == 0 {
                    v___x_5183_ = crate::leanh::lean_box(0);
                    return v___x_5183_;
                } else {
                    v_key_5184_ = crate::leanh::lean_ctor_get(v_x_5182_, 0);
                    v_value_5185_ = crate::leanh::lean_ctor_get(v_x_5182_, 1);
                    v_tail_5186_ = crate::leanh::lean_ctor_get(v_x_5182_, 2);
                    v___x_5187_ = l___private_Lean_Meta_Tactic_Grind_EMatchTheoremPtr_0__Lean_Meta_Grind_isSameEMatchTheoremPtr_unsafe__1(v_key_5184_, v_a_5181_);
                    if v___x_5187_ == 0 {
                        v_x_5182_ = v_tail_5186_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_5185_);
                        v___x_5189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5189_, 0, v_value_5185_);
                        return v___x_5189_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0_spec__0___redArg___boxed(
    mut v_a_5190_: *mut crate::leanh::LeanObject,
    mut v_x_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5192_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0_spec__0___redArg(v_a_5190_, v_x_5191_);
    crate::leanh::lean_dec(v_x_5191_);
    crate::leanh::lean_dec_ref(v_a_5190_);
    return v_res_5192_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0___redArg(
    mut v_m_5193_: *mut crate::leanh::LeanObject,
    mut v_a_5194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: u64 = 0;
    let mut v___x_5198_: u64 = 0;
    let mut v___x_5199_: u64 = 0;
    let mut v_fold_5200_: u64 = 0;
    let mut v___x_5201_: u64 = 0;
    let mut v___x_5202_: u64 = 0;
    let mut v___x_5203_: u64 = 0;
    let mut v___x_5204_: usize = 0;
    let mut v___x_5205_: usize = 0;
    let mut v___x_5206_: usize = 0;
    let mut v___x_5207_: usize = 0;
    let mut v___x_5208_: usize = 0;
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_5195_ = crate::leanh::lean_ctor_get(v_m_5193_, 1);
    v___x_5196_ = lean_array_get_size(v_buckets_5195_);
    v___x_5197_ = l_Lean_Meta_Grind_hashEMatchTheoremPtr_unsafe__1(v_a_5194_);
    v___x_5198_ = 32u64;
    v___x_5199_ = lean_uint64_shift_right(v___x_5197_, v___x_5198_);
    v_fold_5200_ = lean_uint64_xor(v___x_5197_, v___x_5199_);
    v___x_5201_ = 16u64;
    v___x_5202_ = lean_uint64_shift_right(v_fold_5200_, v___x_5201_);
    v___x_5203_ = lean_uint64_xor(v_fold_5200_, v___x_5202_);
    v___x_5204_ = lean_uint64_to_usize(v___x_5203_);
    v___x_5205_ = lean_usize_of_nat(v___x_5196_);
    v___x_5206_ = 1usize;
    v___x_5207_ = lean_usize_sub(v___x_5205_, v___x_5206_);
    v___x_5208_ = lean_usize_land(v___x_5204_, v___x_5207_);
    v___x_5209_ = lean_array_uget_borrowed(v_buckets_5195_, v___x_5208_);
    v___x_5210_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0_spec__0___redArg(v_a_5194_, v___x_5209_);
    return v___x_5210_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0___redArg___boxed(
    mut v_m_5211_: *mut crate::leanh::LeanObject,
    mut v_a_5212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5213_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0___redArg(v_m_5211_, v_a_5212_);
    crate::leanh::lean_dec_ref(v_a_5212_);
    crate::leanh::lean_dec_ref(v_m_5211_);
    return v_res_5213_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5214_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5214_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5215_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__0);
    v___x_5216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5216_, 0, v___x_5215_);
    return v___x_5216_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5217_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__1);
    v___x_5218_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5219_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5219_, 0, v___x_5218_);
    crate::leanh::lean_ctor_set(v___x_5219_, 1, v___x_5218_);
    crate::leanh::lean_ctor_set(v___x_5219_, 2, v___x_5218_);
    crate::leanh::lean_ctor_set(v___x_5219_, 3, v___x_5218_);
    crate::leanh::lean_ctor_set(v___x_5219_, 4, v___x_5217_);
    crate::leanh::lean_ctor_set(v___x_5219_, 5, v___x_5217_);
    crate::leanh::lean_ctor_set(v___x_5219_, 6, v___x_5217_);
    crate::leanh::lean_ctor_set(v___x_5219_, 7, v___x_5217_);
    crate::leanh::lean_ctor_set(v___x_5219_, 8, v___x_5217_);
    crate::leanh::lean_ctor_set(v___x_5219_, 9, v___x_5217_);
    return v___x_5219_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5220_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5221_ = lean_mk_empty_array_with_capacity(v___x_5220_);
    v___x_5222_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5222_, 0, v___x_5221_);
    return v___x_5222_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5223_: usize = 0;
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5223_ = 5usize;
    v___x_5224_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5225_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5226_ = lean_mk_empty_array_with_capacity(v___x_5225_);
    v___x_5227_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__3);
    v___x_5228_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5228_, 0, v___x_5227_);
    crate::leanh::lean_ctor_set(v___x_5228_, 1, v___x_5226_);
    crate::leanh::lean_ctor_set(v___x_5228_, 2, v___x_5224_);
    crate::leanh::lean_ctor_set(v___x_5228_, 3, v___x_5224_);
    crate::leanh::lean_ctor_set_usize(v___x_5228_, 4, v___x_5223_);
    return v___x_5228_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5229_ = crate::leanh::lean_box(1);
    v___x_5230_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__4);
    v___x_5231_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__1);
    v___x_5232_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5232_, 0, v___x_5231_);
    crate::leanh::lean_ctor_set(v___x_5232_, 1, v___x_5230_);
    crate::leanh::lean_ctor_set(v___x_5232_, 2, v___x_5229_);
    return v___x_5232_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2(
    mut v_msgData_5233_: *mut crate::leanh::LeanObject,
    mut v___y_5234_: *mut crate::leanh::LeanObject,
    mut v___y_5235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5237_ = lean_st_ref_get(v___y_5235_);
    v_env_5238_ = crate::leanh::lean_ctor_get(v___x_5237_, 0);
    crate::leanh::lean_inc_ref(v_env_5238_);
    crate::leanh::lean_dec(v___x_5237_);
    v_options_5239_ = crate::leanh::lean_ctor_get(v___y_5234_, 2);
    v___x_5240_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__2);
    v___x_5241_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___closed__5);
    crate::leanh::lean_inc_ref(v_options_5239_);
    v___x_5242_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5242_, 0, v_env_5238_);
    crate::leanh::lean_ctor_set(v___x_5242_, 1, v___x_5240_);
    crate::leanh::lean_ctor_set(v___x_5242_, 2, v___x_5241_);
    crate::leanh::lean_ctor_set(v___x_5242_, 3, v_options_5239_);
    v___x_5243_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5243_, 0, v___x_5242_);
    crate::leanh::lean_ctor_set(v___x_5243_, 1, v_msgData_5233_);
    v___x_5244_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5244_, 0, v___x_5243_);
    return v___x_5244_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2___boxed(
    mut v_msgData_5245_: *mut crate::leanh::LeanObject,
    mut v___y_5246_: *mut crate::leanh::LeanObject,
    mut v___y_5247_: *mut crate::leanh::LeanObject,
    mut v___y_5248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5249_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2(v_msgData_5245_, v___y_5246_, v___y_5247_);
    crate::leanh::lean_dec(v___y_5247_);
    crate::leanh::lean_dec_ref(v___y_5246_);
    return v_res_5249_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1___redArg(
    mut v_msg_5250_: *mut crate::leanh::LeanObject,
    mut v___y_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5259_: u8 = 0;
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5254_ = crate::leanh::lean_ctor_get(v___y_5251_, 5);
                v___x_5255_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1_spec__2(v_msg_5250_, v___y_5251_, v___y_5252_);
                v_a_5256_ = crate::leanh::lean_ctor_get(v___x_5255_, 0);
                v_isSharedCheck_5264_ = (!crate::leanh::lean_is_exclusive(v___x_5255_)) as u8;
                if v_isSharedCheck_5264_ == 0 {
                    v___x_5258_ = v___x_5255_;
                    v_isShared_5259_ = v_isSharedCheck_5264_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5256_);
                    crate::leanh::lean_dec(v___x_5255_);
                    v___x_5258_ = crate::leanh::lean_box(0);
                    v_isShared_5259_ = v_isSharedCheck_5264_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5254_);
                v___x_5260_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5260_, 0, v_ref_5254_);
                crate::leanh::lean_ctor_set(v___x_5260_, 1, v_a_5256_);
                if v_isShared_5259_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5258_, 1);
                    crate::leanh::lean_ctor_set(v___x_5258_, 0, v___x_5260_);
                    v___x_5262_ = v___x_5258_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5260_);
                    v___x_5262_ = v_reuseFailAlloc_5263_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1___redArg___boxed(
    mut v_msg_5265_: *mut crate::leanh::LeanObject,
    mut v___y_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5269_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1___redArg(v_msg_5265_, v___y_5266_, v___y_5267_);
    crate::leanh::lean_dec(v___y_5267_);
    crate::leanh::lean_dec_ref(v___y_5266_);
    return v_res_5269_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___closed__0;
    v___x_5272_ = l_Lean_stringToMessageData(v___x_5271_);
    return v___x_5272_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2(
    mut v_map_5273_: *mut crate::leanh::LeanObject,
    mut v_as_5274_: *mut crate::leanh::LeanObject,
    mut v_sz_5275_: usize,
    mut v_i_5276_: usize,
    mut v_b_5277_: *mut crate::leanh::LeanObject,
    mut v___y_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: usize = 0;
    let mut v___x_5284_: usize = 0;
    let mut v___x_5286_: u8 = 0;
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5298_: u8 = 0;
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5302_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5286_ = lean_usize_dec_lt(v_i_5276_, v_sz_5275_);
                if v___x_5286_ == 0 {
                    v___x_5287_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5287_, 0, v_b_5277_);
                    return v___x_5287_;
                } else {
                    v_a_5288_ = lean_array_uget_borrowed(v_as_5274_, v_i_5276_);
                    v___x_5289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0___redArg(v_map_5273_, v_a_5288_);
                    if crate::leanh::lean_obj_tag(v___x_5289_) == 1 {
                        v_val_5290_ = crate::leanh::lean_ctor_get(v___x_5289_, 0);
                        crate::leanh::lean_inc(v_val_5290_);
                        crate::leanh::lean_dec_ref_known(v___x_5289_, 1);
                        v___x_5291_ = crate::leanh::lean_box((v___x_5286_) as usize);
                        v___x_5292_ = lean_array_set(v_b_5277_, v_val_5290_, v___x_5291_);
                        crate::leanh::lean_dec(v_val_5290_);
                        v_a_5282_ = v___x_5292_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5289_);
                        v___x_5293_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___closed__1);
                        v___x_5294_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1___redArg(v___x_5293_, v___y_5278_, v___y_5279_);
                        if crate::leanh::lean_obj_tag(v___x_5294_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5294_, 1);
                            v_a_5282_ = v_b_5277_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_5277_);
                            v_a_5295_ = crate::leanh::lean_ctor_get(v___x_5294_, 0);
                            v_isSharedCheck_5302_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5294_)) as u8;
                            if v_isSharedCheck_5302_ == 0 {
                                v___x_5297_ = v___x_5294_;
                                v_isShared_5298_ = v_isSharedCheck_5302_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5295_);
                                crate::leanh::lean_dec(v___x_5294_);
                                v___x_5297_ = crate::leanh::lean_box(0);
                                v_isShared_5298_ = v_isSharedCheck_5302_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5283_ = 1usize;
                v___x_5284_ = lean_usize_add(v_i_5276_, v___x_5283_);
                v_i_5276_ = v___x_5284_;
                v_b_5277_ = v_a_5282_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5298_ == 0 {
                    v___x_5300_ = v___x_5297_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5301_, 0, v_a_5295_);
                    v___x_5300_ = v_reuseFailAlloc_5301_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2___boxed(
    mut v_map_5303_: *mut crate::leanh::LeanObject,
    mut v_as_5304_: *mut crate::leanh::LeanObject,
    mut v_sz_5305_: *mut crate::leanh::LeanObject,
    mut v_i_5306_: *mut crate::leanh::LeanObject,
    mut v_b_5307_: *mut crate::leanh::LeanObject,
    mut v___y_5308_: *mut crate::leanh::LeanObject,
    mut v___y_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5311_: usize = 0;
    let mut v_i_boxed_5312_: usize = 0;
    let mut v_res_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5311_ = crate::leanh::lean_unbox_usize(v_sz_5305_);
    crate::leanh::lean_dec(v_sz_5305_);
    v_i_boxed_5312_ = crate::leanh::lean_unbox_usize(v_i_5306_);
    crate::leanh::lean_dec(v_i_5306_);
    v_res_5313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2(v_map_5303_, v_as_5304_, v_sz_boxed_5311_, v_i_boxed_5312_, v_b_5307_, v___y_5308_, v___y_5309_);
    crate::leanh::lean_dec(v___y_5309_);
    crate::leanh::lean_dec_ref(v___y_5308_);
    crate::leanh::lean_dec_ref(v_as_5304_);
    crate::leanh::lean_dec_ref(v_map_5303_);
    return v_res_5313_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask(
    mut v_map_5314_: *mut crate::leanh::LeanObject,
    mut v_thms_5315_: *mut crate::leanh::LeanObject,
    mut v_a_5316_: *mut crate::leanh::LeanObject,
    mut v_a_5317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: u8 = 0;
    let mut v___x_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5323_: usize = 0;
    let mut v___x_5324_: usize = 0;
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_5319_ = crate::leanh::lean_ctor_get(v_map_5314_, 0);
    v___x_5320_ = 0;
    v___x_5321_ = crate::leanh::lean_box((v___x_5320_) as usize);
    crate::leanh::lean_inc(v_size_5319_);
    v_result_5322_ = lean_mk_array(v_size_5319_, v___x_5321_);
    v_sz_5323_ = lean_array_size(v_thms_5315_);
    v___x_5324_ = 0usize;
    v___x_5325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__2(v_map_5314_, v_thms_5315_, v_sz_5323_, v___x_5324_, v_result_5322_, v_a_5316_, v_a_5317_);
    crate::leanh::lean_dec_ref(v_map_5314_);
    return v___x_5325_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask___boxed(
    mut v_map_5326_: *mut crate::leanh::LeanObject,
    mut v_thms_5327_: *mut crate::leanh::LeanObject,
    mut v_a_5328_: *mut crate::leanh::LeanObject,
    mut v_a_5329_: *mut crate::leanh::LeanObject,
    mut v_a_5330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5331_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask(
        v_map_5326_,
        v_thms_5327_,
        v_a_5328_,
        v_a_5329_,
    );
    crate::leanh::lean_dec(v_a_5329_);
    crate::leanh::lean_dec_ref(v_a_5328_);
    crate::leanh::lean_dec_ref(v_thms_5327_);
    return v_res_5331_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0(
    mut v_00_u03b2_5332_: *mut crate::leanh::LeanObject,
    mut v_m_5333_: *mut crate::leanh::LeanObject,
    mut v_a_5334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0___redArg(v_m_5333_, v_a_5334_);
    return v___x_5335_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0___boxed(
    mut v_00_u03b2_5336_: *mut crate::leanh::LeanObject,
    mut v_m_5337_: *mut crate::leanh::LeanObject,
    mut v_a_5338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5339_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0(v_00_u03b2_5336_, v_m_5337_, v_a_5338_);
    crate::leanh::lean_dec_ref(v_a_5338_);
    crate::leanh::lean_dec_ref(v_m_5337_);
    return v_res_5339_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1(
    mut v_00_u03b1_5340_: *mut crate::leanh::LeanObject,
    mut v_msg_5341_: *mut crate::leanh::LeanObject,
    mut v___y_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5345_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1___redArg(v_msg_5341_, v___y_5342_, v___y_5343_);
    return v___x_5345_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1___boxed(
    mut v_00_u03b1_5346_: *mut crate::leanh::LeanObject,
    mut v_msg_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
    mut v___y_5349_: *mut crate::leanh::LeanObject,
    mut v___y_5350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5351_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__1(v_00_u03b1_5346_, v_msg_5347_, v___y_5348_, v___y_5349_);
    crate::leanh::lean_dec(v___y_5349_);
    crate::leanh::lean_dec_ref(v___y_5348_);
    return v_res_5351_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0_spec__0(
    mut v_00_u03b2_5352_: *mut crate::leanh::LeanObject,
    mut v_a_5353_: *mut crate::leanh::LeanObject,
    mut v_x_5354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5355_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0_spec__0___redArg(v_a_5353_, v_x_5354_);
    return v___x_5355_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0_spec__0___boxed(
    mut v_00_u03b2_5356_: *mut crate::leanh::LeanObject,
    mut v_a_5357_: *mut crate::leanh::LeanObject,
    mut v_x_5358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5359_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask_spec__0_spec__0(v_00_u03b2_5356_, v_a_5357_, v_x_5358_);
    crate::leanh::lean_dec(v_x_5358_);
    crate::leanh::lean_dec_ref(v_a_5357_);
    return v_res_5359_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms_spec__0___redArg(
    mut v_upperBound_5360_: *mut crate::leanh::LeanObject,
    mut v_mask_5361_: *mut crate::leanh::LeanObject,
    mut v_thms_5362_: *mut crate::leanh::LeanObject,
    mut v_a_5363_: *mut crate::leanh::LeanObject,
    mut v_b_5364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: u8 = 0;
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: u8 = 0;
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5370_ = lean_nat_dec_lt(v_a_5363_, v_upperBound_5360_);
                if v___x_5370_ == 0 {
                    crate::leanh::lean_dec(v_a_5363_);
                    return v_b_5364_;
                } else {
                    v___x_5371_ = lean_array_fget_borrowed(v_mask_5361_, v_a_5363_);
                    v___x_5372_ = (crate::leanh::lean_unbox(v___x_5371_) as u8);
                    if v___x_5372_ == 0 {
                        v_a_5366_ = v_b_5364_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5373_ = l_Lean_Meta_Grind_instInhabitedEMatchTheorem_default;
                        v___x_5374_ = lean_array_get_borrowed(v___x_5373_, v_thms_5362_, v_a_5363_);
                        crate::leanh::lean_inc(v___x_5374_);
                        v___x_5375_ = lean_array_push(v_b_5364_, v___x_5374_);
                        v_a_5366_ = v___x_5375_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5367_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5368_ = lean_nat_add(v_a_5363_, v___x_5367_);
                crate::leanh::lean_dec(v_a_5363_);
                v_a_5363_ = v___x_5368_;
                v_b_5364_ = v_a_5366_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms_spec__0___redArg___boxed(
    mut v_upperBound_5376_: *mut crate::leanh::LeanObject,
    mut v_mask_5377_: *mut crate::leanh::LeanObject,
    mut v_thms_5378_: *mut crate::leanh::LeanObject,
    mut v_a_5379_: *mut crate::leanh::LeanObject,
    mut v_b_5380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5381_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms_spec__0___redArg(v_upperBound_5376_, v_mask_5377_, v_thms_5378_, v_a_5379_, v_b_5380_);
    crate::leanh::lean_dec_ref(v_thms_5378_);
    crate::leanh::lean_dec_ref(v_mask_5377_);
    crate::leanh::lean_dec(v_upperBound_5376_);
    return v_res_5381_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms(
    mut v_thms_5382_: *mut crate::leanh::LeanObject,
    mut v_mask_5383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5384_ = lean_array_get_size(v_mask_5383_);
    v___x_5385_ = crate::leanh::lean_unsigned_to_nat(0);
    v_result_5386_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__2;
    v___x_5387_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms_spec__0___redArg(v___x_5384_, v_mask_5383_, v_thms_5382_, v___x_5385_, v_result_5386_);
    return v___x_5387_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms___boxed(
    mut v_thms_5388_: *mut crate::leanh::LeanObject,
    mut v_mask_5389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5390_ =
        l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms(
            v_thms_5388_,
            v_mask_5389_,
        );
    crate::leanh::lean_dec_ref(v_mask_5389_);
    crate::leanh::lean_dec_ref(v_thms_5388_);
    return v_res_5390_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms_spec__0(
    mut v_upperBound_5391_: *mut crate::leanh::LeanObject,
    mut v_mask_5392_: *mut crate::leanh::LeanObject,
    mut v_thms_5393_: *mut crate::leanh::LeanObject,
    mut v_inst_5394_: *mut crate::leanh::LeanObject,
    mut v_R_5395_: *mut crate::leanh::LeanObject,
    mut v_a_5396_: *mut crate::leanh::LeanObject,
    mut v_b_5397_: *mut crate::leanh::LeanObject,
    mut v_c_5398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms_spec__0___redArg(v_upperBound_5391_, v_mask_5392_, v_thms_5393_, v_a_5396_, v_b_5397_);
    return v___x_5399_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms_spec__0___boxed(
    mut v_upperBound_5400_: *mut crate::leanh::LeanObject,
    mut v_mask_5401_: *mut crate::leanh::LeanObject,
    mut v_thms_5402_: *mut crate::leanh::LeanObject,
    mut v_inst_5403_: *mut crate::leanh::LeanObject,
    mut v_R_5404_: *mut crate::leanh::LeanObject,
    mut v_a_5405_: *mut crate::leanh::LeanObject,
    mut v_b_5406_: *mut crate::leanh::LeanObject,
    mut v_c_5407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5408_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms_spec__0(v_upperBound_5400_, v_mask_5401_, v_thms_5402_, v_inst_5403_, v_R_5404_, v_a_5405_, v_b_5406_, v_c_5407_);
    crate::leanh::lean_dec_ref(v_thms_5402_);
    crate::leanh::lean_dec_ref(v_mask_5401_);
    crate::leanh::lean_dec(v_upperBound_5400_);
    return v_res_5408_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__0___redArg(
    mut v_e_5409_: *mut crate::leanh::LeanObject,
    mut v___y_5410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5412_: u8 = 0;
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5426_: u8 = 0;
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5432_: u8 = 0;
    let mut v_unused_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5412_ = l_Lean_Expr_hasMVar(v_e_5409_);
                if v___x_5412_ == 0 {
                    v___x_5413_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5413_, 0, v_e_5409_);
                    return v___x_5413_;
                } else {
                    v___x_5414_ = lean_st_ref_get(v___y_5410_);
                    v_mctx_5415_ = crate::leanh::lean_ctor_get(v___x_5414_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5415_);
                    crate::leanh::lean_dec(v___x_5414_);
                    v___x_5416_ = l_Lean_instantiateMVarsCore(v_mctx_5415_, v_e_5409_);
                    v_fst_5417_ = crate::leanh::lean_ctor_get(v___x_5416_, 0);
                    crate::leanh::lean_inc(v_fst_5417_);
                    v_snd_5418_ = crate::leanh::lean_ctor_get(v___x_5416_, 1);
                    crate::leanh::lean_inc(v_snd_5418_);
                    crate::leanh::lean_dec_ref(v___x_5416_);
                    v___x_5419_ = lean_st_ref_take(v___y_5410_);
                    v_cache_5420_ = crate::leanh::lean_ctor_get(v___x_5419_, 1);
                    v_zetaDeltaFVarIds_5421_ = crate::leanh::lean_ctor_get(v___x_5419_, 2);
                    v_postponed_5422_ = crate::leanh::lean_ctor_get(v___x_5419_, 3);
                    v_diag_5423_ = crate::leanh::lean_ctor_get(v___x_5419_, 4);
                    v_isSharedCheck_5432_ = (!crate::leanh::lean_is_exclusive(v___x_5419_)) as u8;
                    if v_isSharedCheck_5432_ == 0 {
                        v_unused_5433_ = crate::leanh::lean_ctor_get(v___x_5419_, 0);
                        crate::leanh::lean_dec(v_unused_5433_);
                        v___x_5425_ = v___x_5419_;
                        v_isShared_5426_ = v_isSharedCheck_5432_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5423_);
                        crate::leanh::lean_inc(v_postponed_5422_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5421_);
                        crate::leanh::lean_inc(v_cache_5420_);
                        crate::leanh::lean_dec(v___x_5419_);
                        v___x_5425_ = crate::leanh::lean_box(0);
                        v_isShared_5426_ = v_isSharedCheck_5432_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5426_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5425_, 0, v_snd_5418_);
                    v___x_5428_ = v___x_5425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5431_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_snd_5418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5431_, 1, v_cache_5420_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5431_,
                        2,
                        v_zetaDeltaFVarIds_5421_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5431_, 3, v_postponed_5422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5431_, 4, v_diag_5423_);
                    v___x_5428_ = v_reuseFailAlloc_5431_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5429_ = lean_st_ref_set(v___y_5410_, v___x_5428_);
                v___x_5430_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5430_, 0, v_fst_5417_);
                return v___x_5430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__0___redArg___boxed(
    mut v_e_5434_: *mut crate::leanh::LeanObject,
    mut v___y_5435_: *mut crate::leanh::LeanObject,
    mut v___y_5436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5437_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__0___redArg(
            v_e_5434_,
            v___y_5435_,
        );
    crate::leanh::lean_dec(v___y_5435_);
    return v_res_5437_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__0(
    mut v_e_5438_: *mut crate::leanh::LeanObject,
    mut v___y_5439_: *mut crate::leanh::LeanObject,
    mut v___y_5440_: *mut crate::leanh::LeanObject,
    mut v___y_5441_: *mut crate::leanh::LeanObject,
    mut v___y_5442_: *mut crate::leanh::LeanObject,
    mut v___y_5443_: *mut crate::leanh::LeanObject,
    mut v___y_5444_: *mut crate::leanh::LeanObject,
    mut v___y_5445_: *mut crate::leanh::LeanObject,
    mut v___y_5446_: *mut crate::leanh::LeanObject,
    mut v___y_5447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5449_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__0___redArg(
            v_e_5438_,
            v___y_5445_,
        );
    return v___x_5449_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__0___boxed(
    mut v_e_5450_: *mut crate::leanh::LeanObject,
    mut v___y_5451_: *mut crate::leanh::LeanObject,
    mut v___y_5452_: *mut crate::leanh::LeanObject,
    mut v___y_5453_: *mut crate::leanh::LeanObject,
    mut v___y_5454_: *mut crate::leanh::LeanObject,
    mut v___y_5455_: *mut crate::leanh::LeanObject,
    mut v___y_5456_: *mut crate::leanh::LeanObject,
    mut v___y_5457_: *mut crate::leanh::LeanObject,
    mut v___y_5458_: *mut crate::leanh::LeanObject,
    mut v___y_5459_: *mut crate::leanh::LeanObject,
    mut v___y_5460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5461_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__0(
        v_e_5450_,
        v___y_5451_,
        v___y_5452_,
        v___y_5453_,
        v___y_5454_,
        v___y_5455_,
        v___y_5456_,
        v___y_5457_,
        v___y_5458_,
        v___y_5459_,
    );
    crate::leanh::lean_dec(v___y_5459_);
    crate::leanh::lean_dec_ref(v___y_5458_);
    crate::leanh::lean_dec(v___y_5457_);
    crate::leanh::lean_dec_ref(v___y_5456_);
    crate::leanh::lean_dec(v___y_5455_);
    crate::leanh::lean_dec_ref(v___y_5454_);
    crate::leanh::lean_dec(v___y_5453_);
    crate::leanh::lean_dec_ref(v___y_5452_);
    crate::leanh::lean_dec(v___y_5451_);
    return v_res_5461_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instantiate_x27___lam__0(
    mut v_goal_5462_: *mut crate::leanh::LeanObject,
    mut v___x_5463_: *mut crate::leanh::LeanObject,
    mut v___y_5464_: *mut crate::leanh::LeanObject,
    mut v___y_5465_: *mut crate::leanh::LeanObject,
    mut v___y_5466_: *mut crate::leanh::LeanObject,
    mut v___y_5467_: *mut crate::leanh::LeanObject,
    mut v___y_5468_: *mut crate::leanh::LeanObject,
    mut v___y_5469_: *mut crate::leanh::LeanObject,
    mut v___y_5470_: *mut crate::leanh::LeanObject,
    mut v___y_5471_: *mut crate::leanh::LeanObject,
    mut v___y_5472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5479_: u8 = 0;
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5485_: u8 = 0;
    let mut v_a_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5489_: u8 = 0;
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5474_ = lean_st_mk_ref(v_goal_5462_);
                v___x_5475_ = l_Lean_Meta_Grind_ematch_x27(
                    v___x_5463_,
                    v___x_5474_,
                    v___y_5464_,
                    v___y_5465_,
                    v___y_5466_,
                    v___y_5467_,
                    v___y_5468_,
                    v___y_5469_,
                    v___y_5470_,
                    v___y_5471_,
                    v___y_5472_,
                );
                if crate::leanh::lean_obj_tag(v___x_5475_) == 0 {
                    v_a_5476_ = crate::leanh::lean_ctor_get(v___x_5475_, 0);
                    v_isSharedCheck_5485_ = (!crate::leanh::lean_is_exclusive(v___x_5475_)) as u8;
                    if v_isSharedCheck_5485_ == 0 {
                        v___x_5478_ = v___x_5475_;
                        v_isShared_5479_ = v_isSharedCheck_5485_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5476_);
                        crate::leanh::lean_dec(v___x_5475_);
                        v___x_5478_ = crate::leanh::lean_box(0);
                        v_isShared_5479_ = v_isSharedCheck_5485_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5474_);
                    v_a_5486_ = crate::leanh::lean_ctor_get(v___x_5475_, 0);
                    v_isSharedCheck_5493_ = (!crate::leanh::lean_is_exclusive(v___x_5475_)) as u8;
                    if v_isSharedCheck_5493_ == 0 {
                        v___x_5488_ = v___x_5475_;
                        v_isShared_5489_ = v_isSharedCheck_5493_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5486_);
                        crate::leanh::lean_dec(v___x_5475_);
                        v___x_5488_ = crate::leanh::lean_box(0);
                        v_isShared_5489_ = v_isSharedCheck_5493_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5480_ = lean_st_ref_get(v___x_5474_);
                crate::leanh::lean_dec(v___x_5474_);
                v___x_5481_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5481_, 0, v_a_5476_);
                crate::leanh::lean_ctor_set(v___x_5481_, 1, v___x_5480_);
                if v_isShared_5479_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5478_, 0, v___x_5481_);
                    v___x_5483_ = v___x_5478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5484_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5481_);
                    v___x_5483_ = v_reuseFailAlloc_5484_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5483_;
            }
            3 => {
                if v_isShared_5489_ == 0 {
                    v___x_5491_ = v___x_5488_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_a_5486_);
                    v___x_5491_ = v_reuseFailAlloc_5492_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5491_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_instantiate_x27___lam__0___boxed(
    mut v_goal_5494_: *mut crate::leanh::LeanObject,
    mut v___x_5495_: *mut crate::leanh::LeanObject,
    mut v___y_5496_: *mut crate::leanh::LeanObject,
    mut v___y_5497_: *mut crate::leanh::LeanObject,
    mut v___y_5498_: *mut crate::leanh::LeanObject,
    mut v___y_5499_: *mut crate::leanh::LeanObject,
    mut v___y_5500_: *mut crate::leanh::LeanObject,
    mut v___y_5501_: *mut crate::leanh::LeanObject,
    mut v___y_5502_: *mut crate::leanh::LeanObject,
    mut v___y_5503_: *mut crate::leanh::LeanObject,
    mut v___y_5504_: *mut crate::leanh::LeanObject,
    mut v___y_5505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5506_ = l_Lean_Meta_Grind_Action_instantiate_x27___lam__0(
        v_goal_5494_,
        v___x_5495_,
        v___y_5496_,
        v___y_5497_,
        v___y_5498_,
        v___y_5499_,
        v___y_5500_,
        v___y_5501_,
        v___y_5502_,
        v___y_5503_,
        v___y_5504_,
    );
    crate::leanh::lean_dec(v___y_5504_);
    crate::leanh::lean_dec_ref(v___y_5503_);
    crate::leanh::lean_dec(v___y_5502_);
    crate::leanh::lean_dec_ref(v___y_5501_);
    crate::leanh::lean_dec(v___y_5500_);
    crate::leanh::lean_dec_ref(v___y_5499_);
    crate::leanh::lean_dec(v___y_5498_);
    crate::leanh::lean_dec_ref(v___y_5497_);
    crate::leanh::lean_dec(v___y_5496_);
    return v_res_5506_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instantiate_x27___lam__1(
    mut v_fst_5508_: *mut crate::leanh::LeanObject,
    mut v_goal_5509_: *mut crate::leanh::LeanObject,
    mut v_seq_5510_: *mut crate::leanh::LeanObject,
    mut v_a_5511_: *mut crate::leanh::LeanObject,
    mut v_mask_5512_: *mut crate::leanh::LeanObject,
    mut v___y_5513_: *mut crate::leanh::LeanObject,
    mut v___y_5514_: *mut crate::leanh::LeanObject,
    mut v___y_5515_: *mut crate::leanh::LeanObject,
    mut v___y_5516_: *mut crate::leanh::LeanObject,
    mut v___y_5517_: *mut crate::leanh::LeanObject,
    mut v___y_5518_: *mut crate::leanh::LeanObject,
    mut v___y_5519_: *mut crate::leanh::LeanObject,
    mut v___y_5520_: *mut crate::leanh::LeanObject,
    mut v___y_5521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: u8 = 0;
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5533_: u8 = 0;
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5537_: u8 = 0;
    let mut v_a_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5541_: u8 = 0;
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5523_ = l_Lean_Meta_Grind_Action_instantiate_x27___lam__1___closed__0;
                v___x_5524_ = l_Lean_Core_checkSystem(v___x_5523_, v___y_5520_, v___y_5521_);
                if crate::leanh::lean_obj_tag(v___x_5524_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5524_, 1);
                    v___x_5525_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms(v_fst_5508_, v_mask_5512_);
                    v___x_5526_ = 0;
                    crate::leanh::lean_inc_ref(v_goal_5509_);
                    v___x_5527_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkNewSeq(v_goal_5509_, v___x_5525_, v_seq_5510_, v___x_5526_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
                    if crate::leanh::lean_obj_tag(v___x_5527_) == 0 {
                        v_a_5528_ = crate::leanh::lean_ctor_get(v___x_5527_, 0);
                        crate::leanh::lean_inc(v_a_5528_);
                        crate::leanh::lean_dec_ref_known(v___x_5527_, 1);
                        v___x_5529_ = l_Lean_Meta_Grind_Action_checkSeqAt(
                            v_a_5511_,
                            v_goal_5509_,
                            v_a_5528_,
                            v___y_5513_,
                            v___y_5514_,
                            v___y_5515_,
                            v___y_5516_,
                            v___y_5517_,
                            v___y_5518_,
                            v___y_5519_,
                            v___y_5520_,
                            v___y_5521_,
                        );
                        return v___x_5529_;
                    } else {
                        crate::leanh::lean_dec(v_a_5511_);
                        crate::leanh::lean_dec_ref(v_goal_5509_);
                        v_a_5530_ = crate::leanh::lean_ctor_get(v___x_5527_, 0);
                        v_isSharedCheck_5537_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5527_)) as u8;
                        if v_isSharedCheck_5537_ == 0 {
                            v___x_5532_ = v___x_5527_;
                            v_isShared_5533_ = v_isSharedCheck_5537_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5530_);
                            crate::leanh::lean_dec(v___x_5527_);
                            v___x_5532_ = crate::leanh::lean_box(0);
                            v_isShared_5533_ = v_isSharedCheck_5537_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5511_);
                    crate::leanh::lean_dec(v_seq_5510_);
                    crate::leanh::lean_dec_ref(v_goal_5509_);
                    v_a_5538_ = crate::leanh::lean_ctor_get(v___x_5524_, 0);
                    v_isSharedCheck_5545_ = (!crate::leanh::lean_is_exclusive(v___x_5524_)) as u8;
                    if v_isSharedCheck_5545_ == 0 {
                        v___x_5540_ = v___x_5524_;
                        v_isShared_5541_ = v_isSharedCheck_5545_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5538_);
                        crate::leanh::lean_dec(v___x_5524_);
                        v___x_5540_ = crate::leanh::lean_box(0);
                        v_isShared_5541_ = v_isSharedCheck_5545_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5533_ == 0 {
                    v___x_5535_ = v___x_5532_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5530_);
                    v___x_5535_ = v_reuseFailAlloc_5536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5535_;
            }
            3 => {
                if v_isShared_5541_ == 0 {
                    v___x_5543_ = v___x_5540_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_a_5538_);
                    v___x_5543_ = v_reuseFailAlloc_5544_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_instantiate_x27___lam__1___boxed(
    mut v_fst_5546_: *mut crate::leanh::LeanObject,
    mut v_goal_5547_: *mut crate::leanh::LeanObject,
    mut v_seq_5548_: *mut crate::leanh::LeanObject,
    mut v_a_5549_: *mut crate::leanh::LeanObject,
    mut v_mask_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
    mut v___y_5552_: *mut crate::leanh::LeanObject,
    mut v___y_5553_: *mut crate::leanh::LeanObject,
    mut v___y_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
    mut v___y_5558_: *mut crate::leanh::LeanObject,
    mut v___y_5559_: *mut crate::leanh::LeanObject,
    mut v___y_5560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5561_ = l_Lean_Meta_Grind_Action_instantiate_x27___lam__1(
        v_fst_5546_,
        v_goal_5547_,
        v_seq_5548_,
        v_a_5549_,
        v_mask_5550_,
        v___y_5551_,
        v___y_5552_,
        v___y_5553_,
        v___y_5554_,
        v___y_5555_,
        v___y_5556_,
        v___y_5557_,
        v___y_5558_,
        v___y_5559_,
    );
    crate::leanh::lean_dec(v___y_5559_);
    crate::leanh::lean_dec_ref(v___y_5558_);
    crate::leanh::lean_dec(v___y_5557_);
    crate::leanh::lean_dec_ref(v___y_5556_);
    crate::leanh::lean_dec(v___y_5555_);
    crate::leanh::lean_dec_ref(v___y_5554_);
    crate::leanh::lean_dec(v___y_5553_);
    crate::leanh::lean_dec_ref(v___y_5552_);
    crate::leanh::lean_dec(v___y_5551_);
    crate::leanh::lean_dec_ref(v_mask_5550_);
    crate::leanh::lean_dec_ref(v_fst_5546_);
    return v_res_5561_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_a_5564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cur_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5571_: u8 = 0;
    let mut v___x_5572_: u8 = 0;
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5579_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cur_5566_ = crate::leanh::lean_ctor_get(v_a_5564_, 0);
                v_added_5567_ = crate::leanh::lean_ctor_get(v_a_5564_, 1);
                v_numCalls_5568_ = crate::leanh::lean_ctor_get(v_a_5564_, 2);
                v_isSharedCheck_5579_ = (!crate::leanh::lean_is_exclusive(v_a_5564_)) as u8;
                if v_isSharedCheck_5579_ == 0 {
                    v___x_5570_ = v_a_5564_;
                    v_isShared_5571_ = v_isSharedCheck_5579_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numCalls_5568_);
                    crate::leanh::lean_inc(v_added_5567_);
                    crate::leanh::lean_inc(v_cur_5566_);
                    crate::leanh::lean_dec(v_a_5564_);
                    v___x_5570_ = crate::leanh::lean_box(0);
                    v_isShared_5571_ = v_isSharedCheck_5579_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5572_ = 1;
                if v_isShared_5571_ == 0 {
                    v___x_5574_ = v___x_5570_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5578_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_cur_5566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5578_, 1, v_added_5567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5578_, 2, v_numCalls_5568_);
                    v___x_5574_ = v_reuseFailAlloc_5578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5574_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_5572_,
                );
                v___x_5575_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
                v___x_5576_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5576_, 0, v___x_5575_);
                crate::leanh::lean_ctor_set(v___x_5576_, 1, v___x_5574_);
                v___x_5577_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5577_, 0, v___x_5576_);
                return v___x_5577_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_a_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5582_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_a_5580_);
    return v_res_5582_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3(
    mut v_a_5585_: *mut crate::leanh::LeanObject,
    mut v_a_5586_: *mut crate::leanh::LeanObject,
    mut v___y_5587_: *mut crate::leanh::LeanObject,
    mut v___y_5588_: *mut crate::leanh::LeanObject,
    mut v___y_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
    mut v___y_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
    mut v___y_5595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_test_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxCalls_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5600_: u8 = 0;
    let mut v_cur_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_5604_: u8 = 0;
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5607_: u8 = 0;
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5616_: u8 = 0;
    let mut v___x_5617_: u8 = 0;
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5627_: u8 = 0;
    let mut v_fst_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5632_: u8 = 0;
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5635_: u8 = 0;
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5645_: u8 = 0;
    let mut v_unused_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5647_: u8 = 0;
    let mut v_isSharedCheck_5648_: u8 = 0;
    let mut v_isSharedCheck_5649_: u8 = 0;
    let mut v_a_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5653_: u8 = 0;
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5657_: u8 = 0;
    let mut v_reuseFailAlloc_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5659_: u8 = 0;
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: u8 = 0;
    let mut v_numCalls_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_test_5597_ = crate::leanh::lean_ctor_get(v_a_5585_, 1);
                v_maxCalls_5598_ = crate::leanh::lean_ctor_get(v_a_5585_, 2);
                v___x_5663_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5664_ = lean_nat_dec_lt(v___x_5663_, v_maxCalls_5598_);
                if v___x_5664_ == 0 {
                    v___y_5600_ = v___x_5664_;
                    state = 1;
                    continue;
                } else {
                    v_numCalls_5665_ = crate::leanh::lean_ctor_get(v_a_5586_, 2);
                    v___x_5666_ = lean_nat_dec_le(v_maxCalls_5598_, v_numCalls_5665_);
                    v___y_5600_ = v___x_5666_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_5600_ == 0 {
                    v_cur_5601_ = crate::leanh::lean_ctor_get(v_a_5586_, 0);
                    v_added_5602_ = crate::leanh::lean_ctor_get(v_a_5586_, 1);
                    v_numCalls_5603_ = crate::leanh::lean_ctor_get(v_a_5586_, 2);
                    v_found_5604_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_5586_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_isSharedCheck_5659_ = (!crate::leanh::lean_is_exclusive(v_a_5586_)) as u8;
                    if v_isSharedCheck_5659_ == 0 {
                        v___x_5606_ = v_a_5586_;
                        v_isShared_5607_ = v_isSharedCheck_5659_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_numCalls_5603_);
                        crate::leanh::lean_inc(v_added_5602_);
                        crate::leanh::lean_inc(v_cur_5601_);
                        crate::leanh::lean_dec(v_a_5586_);
                        v___x_5606_ = crate::leanh::lean_box(0);
                        v_isShared_5607_ = v_isSharedCheck_5659_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5660_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3___closed__0;
                    v___x_5661_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5661_, 0, v___x_5660_);
                    crate::leanh::lean_ctor_set(v___x_5661_, 1, v_a_5586_);
                    v___x_5662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5662_, 0, v___x_5661_);
                    return v___x_5662_;
                }
            }
            2 => {
                v___x_5608_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5609_ = lean_nat_add(v_numCalls_5603_, v___x_5608_);
                crate::leanh::lean_dec(v_numCalls_5603_);
                crate::leanh::lean_inc_ref(v_cur_5601_);
                if v_isShared_5607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5606_, 2, v___x_5609_);
                    v___x_5611_ = v___x_5606_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5658_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_cur_5601_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 1, v_added_5602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 2, v___x_5609_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5658_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_found_5604_,
                    );
                    v___x_5611_ = v_reuseFailAlloc_5658_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_test_5597_);
                crate::leanh::lean_inc(v___y_5595_);
                crate::leanh::lean_inc_ref(v___y_5594_);
                crate::leanh::lean_inc(v___y_5593_);
                crate::leanh::lean_inc_ref(v___y_5592_);
                crate::leanh::lean_inc(v___y_5591_);
                crate::leanh::lean_inc_ref(v___y_5590_);
                crate::leanh::lean_inc(v___y_5589_);
                crate::leanh::lean_inc_ref(v___y_5588_);
                crate::leanh::lean_inc(v___y_5587_);
                v___x_5612_ = crate::leanh::lean_apply_11(
                    v_test_5597_,
                    v_cur_5601_,
                    v___y_5587_,
                    v___y_5588_,
                    v___y_5589_,
                    v___y_5590_,
                    v___y_5591_,
                    v___y_5592_,
                    v___y_5593_,
                    v___y_5594_,
                    v___y_5595_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5612_) == 0 {
                    v_a_5613_ = crate::leanh::lean_ctor_get(v___x_5612_, 0);
                    v_isSharedCheck_5649_ = (!crate::leanh::lean_is_exclusive(v___x_5612_)) as u8;
                    if v_isSharedCheck_5649_ == 0 {
                        v___x_5615_ = v___x_5612_;
                        v_isShared_5616_ = v_isSharedCheck_5649_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5613_);
                        crate::leanh::lean_dec(v___x_5612_);
                        v___x_5615_ = crate::leanh::lean_box(0);
                        v_isShared_5616_ = v_isSharedCheck_5649_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5611_);
                    v_a_5650_ = crate::leanh::lean_ctor_get(v___x_5612_, 0);
                    v_isSharedCheck_5657_ = (!crate::leanh::lean_is_exclusive(v___x_5612_)) as u8;
                    if v_isSharedCheck_5657_ == 0 {
                        v___x_5652_ = v___x_5612_;
                        v_isShared_5653_ = v_isSharedCheck_5657_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5650_);
                        crate::leanh::lean_dec(v___x_5612_);
                        v___x_5652_ = crate::leanh::lean_box(0);
                        v_isShared_5653_ = v_isSharedCheck_5657_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5617_ = (crate::leanh::lean_unbox(v_a_5613_) as u8);
                if v___x_5617_ == 0 {
                    v___x_5618_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5618_, 0, v_a_5613_);
                    v___x_5619_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5619_, 0, v___x_5618_);
                    crate::leanh::lean_ctor_set(v___x_5619_, 1, v___x_5611_);
                    if v_isShared_5616_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5615_, 0, v___x_5619_);
                        v___x_5621_ = v___x_5615_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5622_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5619_);
                        v___x_5621_ = v_reuseFailAlloc_5622_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5615_);
                    v___x_5623_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v___x_5611_);
                    v_a_5624_ = crate::leanh::lean_ctor_get(v___x_5623_, 0);
                    v_isSharedCheck_5648_ = (!crate::leanh::lean_is_exclusive(v___x_5623_)) as u8;
                    if v_isSharedCheck_5648_ == 0 {
                        v___x_5626_ = v___x_5623_;
                        v_isShared_5627_ = v_isSharedCheck_5648_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5624_);
                        crate::leanh::lean_dec(v___x_5623_);
                        v___x_5626_ = crate::leanh::lean_box(0);
                        v_isShared_5627_ = v_isSharedCheck_5648_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5621_;
            }
            6 => {
                v_fst_5628_ = crate::leanh::lean_ctor_get(v_a_5624_, 0);
                v_snd_5629_ = crate::leanh::lean_ctor_get(v_a_5624_, 1);
                v_isSharedCheck_5647_ = (!crate::leanh::lean_is_exclusive(v_a_5624_)) as u8;
                if v_isSharedCheck_5647_ == 0 {
                    v___x_5631_ = v_a_5624_;
                    v_isShared_5632_ = v_isSharedCheck_5647_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5629_);
                    crate::leanh::lean_inc(v_fst_5628_);
                    crate::leanh::lean_dec(v_a_5624_);
                    v___x_5631_ = crate::leanh::lean_box(0);
                    v_isShared_5632_ = v_isSharedCheck_5647_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_isSharedCheck_5645_ = (!crate::leanh::lean_is_exclusive(v_fst_5628_)) as u8;
                if v_isSharedCheck_5645_ == 0 {
                    v_unused_5646_ = crate::leanh::lean_ctor_get(v_fst_5628_, 0);
                    crate::leanh::lean_dec(v_unused_5646_);
                    v___x_5634_ = v_fst_5628_;
                    v_isShared_5635_ = v_isSharedCheck_5645_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_5628_);
                    v___x_5634_ = crate::leanh::lean_box(0);
                    v_isShared_5635_ = v_isSharedCheck_5645_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_5635_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5634_, 0, v_a_5613_);
                    v___x_5637_ = v___x_5634_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5644_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5644_, 0, v_a_5613_);
                    v___x_5637_ = v_reuseFailAlloc_5644_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5632_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5631_, 0, v___x_5637_);
                    v___x_5639_ = v___x_5631_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5643_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5643_, 0, v___x_5637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5643_, 1, v_snd_5629_);
                    v___x_5639_ = v_reuseFailAlloc_5643_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_5627_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5626_, 0, v___x_5639_);
                    v___x_5641_ = v___x_5626_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5642_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5642_, 0, v___x_5639_);
                    v___x_5641_ = v_reuseFailAlloc_5642_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5641_;
            }
            12 => {
                if v_isShared_5653_ == 0 {
                    v___x_5655_ = v___x_5652_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_a_5650_);
                    v___x_5655_ = v_reuseFailAlloc_5656_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_a_5667_: *mut crate::leanh::LeanObject,
    mut v_a_5668_: *mut crate::leanh::LeanObject,
    mut v___y_5669_: *mut crate::leanh::LeanObject,
    mut v___y_5670_: *mut crate::leanh::LeanObject,
    mut v___y_5671_: *mut crate::leanh::LeanObject,
    mut v___y_5672_: *mut crate::leanh::LeanObject,
    mut v___y_5673_: *mut crate::leanh::LeanObject,
    mut v___y_5674_: *mut crate::leanh::LeanObject,
    mut v___y_5675_: *mut crate::leanh::LeanObject,
    mut v___y_5676_: *mut crate::leanh::LeanObject,
    mut v___y_5677_: *mut crate::leanh::LeanObject,
    mut v___y_5678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5679_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3(v_a_5667_, v_a_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
    crate::leanh::lean_dec(v___y_5677_);
    crate::leanh::lean_dec_ref(v___y_5676_);
    crate::leanh::lean_dec(v___y_5675_);
    crate::leanh::lean_dec_ref(v___y_5674_);
    crate::leanh::lean_dec(v___y_5673_);
    crate::leanh::lean_dec_ref(v___y_5672_);
    crate::leanh::lean_dec(v___y_5671_);
    crate::leanh::lean_dec_ref(v___y_5670_);
    crate::leanh::lean_dec(v___y_5669_);
    crate::leanh::lean_dec_ref(v_a_5667_);
    return v_res_5679_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___lam__0(
    mut v___x_5680_: *mut crate::leanh::LeanObject,
    mut v___x_5681_: *mut crate::leanh::LeanObject,
    mut v_____r_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
    mut v___y_5684_: *mut crate::leanh::LeanObject,
    mut v___y_5685_: *mut crate::leanh::LeanObject,
    mut v___y_5686_: *mut crate::leanh::LeanObject,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
    mut v___y_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
    mut v___y_5690_: *mut crate::leanh::LeanObject,
    mut v___y_5691_: *mut crate::leanh::LeanObject,
    mut v___y_5692_: *mut crate::leanh::LeanObject,
    mut v___y_5693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v_fst_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5704_: u8 = 0;
    let mut v_a_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5708_: u8 = 0;
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5718_: u8 = 0;
    let mut v_isSharedCheck_5719_: u8 = 0;
    let mut v_unused_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5724_: u8 = 0;
    let mut v___x_5725_: u8 = 0;
    let mut v_snd_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5729_: u8 = 0;
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5740_: u8 = 0;
    let mut v_unused_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5745_: u8 = 0;
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5758_: u8 = 0;
    let mut v_unused_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5760_: u8 = 0;
    let mut v_isSharedCheck_5761_: u8 = 0;
    let mut v_a_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5765_: u8 = 0;
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5695_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3(v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_);
                if crate::leanh::lean_obj_tag(v___x_5695_) == 0 {
                    v_a_5696_ = crate::leanh::lean_ctor_get(v___x_5695_, 0);
                    v_isSharedCheck_5761_ = (!crate::leanh::lean_is_exclusive(v___x_5695_)) as u8;
                    if v_isSharedCheck_5761_ == 0 {
                        v___x_5698_ = v___x_5695_;
                        v_isShared_5699_ = v_isSharedCheck_5761_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5696_);
                        crate::leanh::lean_dec(v___x_5695_);
                        v___x_5698_ = crate::leanh::lean_box(0);
                        v_isShared_5699_ = v_isSharedCheck_5761_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5680_);
                    v_a_5762_ = crate::leanh::lean_ctor_get(v___x_5695_, 0);
                    v_isSharedCheck_5769_ = (!crate::leanh::lean_is_exclusive(v___x_5695_)) as u8;
                    if v_isSharedCheck_5769_ == 0 {
                        v___x_5764_ = v___x_5695_;
                        v_isShared_5765_ = v_isSharedCheck_5769_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5762_);
                        crate::leanh::lean_dec(v___x_5695_);
                        v___x_5764_ = crate::leanh::lean_box(0);
                        v_isShared_5765_ = v_isSharedCheck_5769_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5700_ = crate::leanh::lean_ctor_get(v_a_5696_, 0);
                crate::leanh::lean_inc(v_fst_5700_);
                if crate::leanh::lean_obj_tag(v_fst_5700_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_5680_);
                    v_snd_5701_ = crate::leanh::lean_ctor_get(v_a_5696_, 1);
                    v_isSharedCheck_5719_ = (!crate::leanh::lean_is_exclusive(v_a_5696_)) as u8;
                    if v_isSharedCheck_5719_ == 0 {
                        v_unused_5720_ = crate::leanh::lean_ctor_get(v_a_5696_, 0);
                        crate::leanh::lean_dec(v_unused_5720_);
                        v___x_5703_ = v_a_5696_;
                        v_isShared_5704_ = v_isSharedCheck_5719_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5701_);
                        crate::leanh::lean_dec(v_a_5696_);
                        v___x_5703_ = crate::leanh::lean_box(0);
                        v_isShared_5704_ = v_isSharedCheck_5719_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5721_ = crate::leanh::lean_ctor_get(v_fst_5700_, 0);
                    v_isSharedCheck_5760_ = (!crate::leanh::lean_is_exclusive(v_fst_5700_)) as u8;
                    if v_isSharedCheck_5760_ == 0 {
                        v___x_5723_ = v_fst_5700_;
                        v_isShared_5724_ = v_isSharedCheck_5760_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5721_);
                        crate::leanh::lean_dec(v_fst_5700_);
                        v___x_5723_ = crate::leanh::lean_box(0);
                        v_isShared_5724_ = v_isSharedCheck_5760_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_a_5705_ = crate::leanh::lean_ctor_get(v_fst_5700_, 0);
                v_isSharedCheck_5718_ = (!crate::leanh::lean_is_exclusive(v_fst_5700_)) as u8;
                if v_isSharedCheck_5718_ == 0 {
                    v___x_5707_ = v_fst_5700_;
                    v_isShared_5708_ = v_isSharedCheck_5718_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5705_);
                    crate::leanh::lean_dec(v_fst_5700_);
                    v___x_5707_ = crate::leanh::lean_box(0);
                    v_isShared_5708_ = v_isSharedCheck_5718_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5708_ == 0 {
                    v___x_5710_ = v___x_5707_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5717_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5717_, 0, v_a_5705_);
                    v___x_5710_ = v_reuseFailAlloc_5717_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5704_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5703_, 0, v___x_5710_);
                    v___x_5712_ = v___x_5703_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 0, v___x_5710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 1, v_snd_5701_);
                    v___x_5712_ = v_reuseFailAlloc_5716_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5699_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5698_, 0, v___x_5712_);
                    v___x_5714_ = v___x_5698_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5715_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5712_);
                    v___x_5714_ = v_reuseFailAlloc_5715_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5714_;
            }
            7 => {
                v___x_5725_ = (crate::leanh::lean_unbox(v_a_5721_) as u8);
                crate::leanh::lean_dec(v_a_5721_);
                if v___x_5725_ == 0 {
                    v_snd_5726_ = crate::leanh::lean_ctor_get(v_a_5696_, 1);
                    v_isSharedCheck_5740_ = (!crate::leanh::lean_is_exclusive(v_a_5696_)) as u8;
                    if v_isSharedCheck_5740_ == 0 {
                        v_unused_5741_ = crate::leanh::lean_ctor_get(v_a_5696_, 0);
                        crate::leanh::lean_dec(v_unused_5741_);
                        v___x_5728_ = v_a_5696_;
                        v_isShared_5729_ = v_isSharedCheck_5740_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5726_);
                        crate::leanh::lean_dec(v_a_5696_);
                        v___x_5728_ = crate::leanh::lean_box(0);
                        v_isShared_5729_ = v_isSharedCheck_5740_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5680_);
                    v_snd_5742_ = crate::leanh::lean_ctor_get(v_a_5696_, 1);
                    v_isSharedCheck_5758_ = (!crate::leanh::lean_is_exclusive(v_a_5696_)) as u8;
                    if v_isSharedCheck_5758_ == 0 {
                        v_unused_5759_ = crate::leanh::lean_ctor_get(v_a_5696_, 0);
                        crate::leanh::lean_dec(v_unused_5759_);
                        v___x_5744_ = v_a_5696_;
                        v_isShared_5745_ = v_isSharedCheck_5758_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5742_);
                        crate::leanh::lean_dec(v_a_5696_);
                        v___x_5744_ = crate::leanh::lean_box(0);
                        v_isShared_5745_ = v_isSharedCheck_5758_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                v___x_5730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5730_, 0, v___x_5680_);
                if v_isShared_5724_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5723_, 0, v___x_5730_);
                    v___x_5732_ = v___x_5723_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5739_, 0, v___x_5730_);
                    v___x_5732_ = v_reuseFailAlloc_5739_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5729_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5728_, 0, v___x_5732_);
                    v___x_5734_ = v___x_5728_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5738_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5738_, 0, v___x_5732_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5738_, 1, v_snd_5726_);
                    v___x_5734_ = v_reuseFailAlloc_5738_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_5699_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5698_, 0, v___x_5734_);
                    v___x_5736_ = v___x_5698_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5737_, 0, v___x_5734_);
                    v___x_5736_ = v_reuseFailAlloc_5737_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5736_;
            }
            12 => {
                v___x_5746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5746_, 0, v___x_5681_);
                if v_isShared_5745_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5744_, 1, v___x_5681_);
                    crate::leanh::lean_ctor_set(v___x_5744_, 0, v___x_5746_);
                    v___x_5748_ = v___x_5744_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5757_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5757_, 0, v___x_5746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5757_, 1, v___x_5681_);
                    v___x_5748_ = v_reuseFailAlloc_5757_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_5749_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5749_, 0, v___x_5748_);
                if v_isShared_5724_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5723_, 0, v___x_5749_);
                    v___x_5751_ = v___x_5723_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5756_, 0, v___x_5749_);
                    v___x_5751_ = v_reuseFailAlloc_5756_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_5752_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5752_, 0, v___x_5751_);
                crate::leanh::lean_ctor_set(v___x_5752_, 1, v_snd_5742_);
                if v_isShared_5699_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5698_, 0, v___x_5752_);
                    v___x_5754_ = v___x_5698_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5755_, 0, v___x_5752_);
                    v___x_5754_ = v_reuseFailAlloc_5755_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5754_;
            }
            16 => {
                if v_isShared_5765_ == 0 {
                    v___x_5767_ = v___x_5764_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5768_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5762_);
                    v___x_5767_ = v_reuseFailAlloc_5768_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___lam__0___boxed(
    mut v___x_5770_: *mut crate::leanh::LeanObject,
    mut v___x_5771_: *mut crate::leanh::LeanObject,
    mut v_____r_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
    mut v___y_5774_: *mut crate::leanh::LeanObject,
    mut v___y_5775_: *mut crate::leanh::LeanObject,
    mut v___y_5776_: *mut crate::leanh::LeanObject,
    mut v___y_5777_: *mut crate::leanh::LeanObject,
    mut v___y_5778_: *mut crate::leanh::LeanObject,
    mut v___y_5779_: *mut crate::leanh::LeanObject,
    mut v___y_5780_: *mut crate::leanh::LeanObject,
    mut v___y_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
    mut v___y_5784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5785_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___lam__0(v___x_5770_, v___x_5771_, v_____r_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
    crate::leanh::lean_dec(v___y_5783_);
    crate::leanh::lean_dec_ref(v___y_5782_);
    crate::leanh::lean_dec(v___y_5781_);
    crate::leanh::lean_dec_ref(v___y_5780_);
    crate::leanh::lean_dec(v___y_5779_);
    crate::leanh::lean_dec_ref(v___y_5778_);
    crate::leanh::lean_dec(v___y_5777_);
    crate::leanh::lean_dec_ref(v___y_5776_);
    crate::leanh::lean_dec(v___y_5775_);
    crate::leanh::lean_dec_ref(v___y_5773_);
    return v_res_5785_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_i_5786_: *mut crate::leanh::LeanObject,
    mut v_a_5787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cur_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_5792_: u8 = 0;
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5795_: u8 = 0;
    let mut v___x_5796_: u8 = 0;
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cur_5789_ = crate::leanh::lean_ctor_get(v_a_5787_, 0);
                v_added_5790_ = crate::leanh::lean_ctor_get(v_a_5787_, 1);
                v_numCalls_5791_ = crate::leanh::lean_ctor_get(v_a_5787_, 2);
                v_found_5792_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5787_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_5806_ = (!crate::leanh::lean_is_exclusive(v_a_5787_)) as u8;
                if v_isSharedCheck_5806_ == 0 {
                    v___x_5794_ = v_a_5787_;
                    v_isShared_5795_ = v_isSharedCheck_5806_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numCalls_5791_);
                    crate::leanh::lean_inc(v_added_5790_);
                    crate::leanh::lean_inc(v_cur_5789_);
                    crate::leanh::lean_dec(v_a_5787_);
                    v___x_5794_ = crate::leanh::lean_box(0);
                    v_isShared_5795_ = v_isSharedCheck_5806_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5796_ = 1;
                v___x_5797_ = crate::leanh::lean_box((v___x_5796_) as usize);
                v___x_5798_ = lean_array_set(v_cur_5789_, v_i_5786_, v___x_5797_);
                v___x_5799_ = lean_array_push(v_added_5790_, v_i_5786_);
                if v_isShared_5795_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5794_, 1, v___x_5799_);
                    crate::leanh::lean_ctor_set(v___x_5794_, 0, v___x_5798_);
                    v___x_5801_ = v___x_5794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5805_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5805_, 0, v___x_5798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5805_, 1, v___x_5799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5805_, 2, v_numCalls_5791_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5805_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_found_5792_,
                    );
                    v___x_5801_ = v_reuseFailAlloc_5805_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5802_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
                v___x_5803_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5803_, 0, v___x_5802_);
                crate::leanh::lean_ctor_set(v___x_5803_, 1, v___x_5801_);
                v___x_5804_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5804_, 0, v___x_5803_);
                return v___x_5804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_i_5807_: *mut crate::leanh::LeanObject,
    mut v_a_5808_: *mut crate::leanh::LeanObject,
    mut v___y_5809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5810_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__4___redArg(v_i_5807_, v_a_5808_);
    return v_res_5810_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___lam__1(
    mut v_a_5811_: *mut crate::leanh::LeanObject,
    mut v___y_5812_: *mut crate::leanh::LeanObject,
    mut v___f_5813_: *mut crate::leanh::LeanObject,
    mut v___y_5814_: *mut crate::leanh::LeanObject,
    mut v___y_5815_: *mut crate::leanh::LeanObject,
    mut v___y_5816_: *mut crate::leanh::LeanObject,
    mut v___y_5817_: *mut crate::leanh::LeanObject,
    mut v___y_5818_: *mut crate::leanh::LeanObject,
    mut v___y_5819_: *mut crate::leanh::LeanObject,
    mut v___y_5820_: *mut crate::leanh::LeanObject,
    mut v___y_5821_: *mut crate::leanh::LeanObject,
    mut v___y_5822_: *mut crate::leanh::LeanObject,
    mut v___y_5823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5829_: u8 = 0;
    let mut v_fst_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5834_: u8 = 0;
    let mut v_a_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5838_: u8 = 0;
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5848_: u8 = 0;
    let mut v_isSharedCheck_5849_: u8 = 0;
    let mut v_unused_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5854_: u8 = 0;
    let mut v_a_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5858_: u8 = 0;
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5862_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5825_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__4___redArg(v_a_5811_, v___y_5812_);
                if crate::leanh::lean_obj_tag(v___x_5825_) == 0 {
                    v_a_5826_ = crate::leanh::lean_ctor_get(v___x_5825_, 0);
                    v_isSharedCheck_5854_ = (!crate::leanh::lean_is_exclusive(v___x_5825_)) as u8;
                    if v_isSharedCheck_5854_ == 0 {
                        v___x_5828_ = v___x_5825_;
                        v_isShared_5829_ = v_isSharedCheck_5854_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5826_);
                        crate::leanh::lean_dec(v___x_5825_);
                        v___x_5828_ = crate::leanh::lean_box(0);
                        v_isShared_5829_ = v_isSharedCheck_5854_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_5813_);
                    v_a_5855_ = crate::leanh::lean_ctor_get(v___x_5825_, 0);
                    v_isSharedCheck_5862_ = (!crate::leanh::lean_is_exclusive(v___x_5825_)) as u8;
                    if v_isSharedCheck_5862_ == 0 {
                        v___x_5857_ = v___x_5825_;
                        v_isShared_5858_ = v_isSharedCheck_5862_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5855_);
                        crate::leanh::lean_dec(v___x_5825_);
                        v___x_5857_ = crate::leanh::lean_box(0);
                        v_isShared_5858_ = v_isSharedCheck_5862_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5830_ = crate::leanh::lean_ctor_get(v_a_5826_, 0);
                crate::leanh::lean_inc(v_fst_5830_);
                if crate::leanh::lean_obj_tag(v_fst_5830_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_5813_);
                    v_snd_5831_ = crate::leanh::lean_ctor_get(v_a_5826_, 1);
                    v_isSharedCheck_5849_ = (!crate::leanh::lean_is_exclusive(v_a_5826_)) as u8;
                    if v_isSharedCheck_5849_ == 0 {
                        v_unused_5850_ = crate::leanh::lean_ctor_get(v_a_5826_, 0);
                        crate::leanh::lean_dec(v_unused_5850_);
                        v___x_5833_ = v_a_5826_;
                        v_isShared_5834_ = v_isSharedCheck_5849_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5831_);
                        crate::leanh::lean_dec(v_a_5826_);
                        v___x_5833_ = crate::leanh::lean_box(0);
                        v_isShared_5834_ = v_isSharedCheck_5849_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5828_);
                    v_snd_5851_ = crate::leanh::lean_ctor_get(v_a_5826_, 1);
                    crate::leanh::lean_inc(v_snd_5851_);
                    crate::leanh::lean_dec(v_a_5826_);
                    v_a_5852_ = crate::leanh::lean_ctor_get(v_fst_5830_, 0);
                    crate::leanh::lean_inc(v_a_5852_);
                    crate::leanh::lean_dec_ref_known(v_fst_5830_, 1);
                    crate::leanh::lean_inc(v___y_5823_);
                    crate::leanh::lean_inc_ref(v___y_5822_);
                    crate::leanh::lean_inc(v___y_5821_);
                    crate::leanh::lean_inc_ref(v___y_5820_);
                    crate::leanh::lean_inc(v___y_5819_);
                    crate::leanh::lean_inc_ref(v___y_5818_);
                    crate::leanh::lean_inc(v___y_5817_);
                    crate::leanh::lean_inc_ref(v___y_5816_);
                    crate::leanh::lean_inc(v___y_5815_);
                    crate::leanh::lean_inc_ref(v___y_5814_);
                    v___x_5853_ = crate::leanh::lean_apply_13(
                        v___f_5813_,
                        v_a_5852_,
                        v___y_5814_,
                        v_snd_5851_,
                        v___y_5815_,
                        v___y_5816_,
                        v___y_5817_,
                        v___y_5818_,
                        v___y_5819_,
                        v___y_5820_,
                        v___y_5821_,
                        v___y_5822_,
                        v___y_5823_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5853_;
                }
            }
            2 => {
                v_a_5835_ = crate::leanh::lean_ctor_get(v_fst_5830_, 0);
                v_isSharedCheck_5848_ = (!crate::leanh::lean_is_exclusive(v_fst_5830_)) as u8;
                if v_isSharedCheck_5848_ == 0 {
                    v___x_5837_ = v_fst_5830_;
                    v_isShared_5838_ = v_isSharedCheck_5848_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5835_);
                    crate::leanh::lean_dec(v_fst_5830_);
                    v___x_5837_ = crate::leanh::lean_box(0);
                    v_isShared_5838_ = v_isSharedCheck_5848_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5838_ == 0 {
                    v___x_5840_ = v___x_5837_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5847_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_a_5835_);
                    v___x_5840_ = v_reuseFailAlloc_5847_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5834_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5833_, 0, v___x_5840_);
                    v___x_5842_ = v___x_5833_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5846_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5846_, 0, v___x_5840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5846_, 1, v_snd_5831_);
                    v___x_5842_ = v_reuseFailAlloc_5846_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5829_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5828_, 0, v___x_5842_);
                    v___x_5844_ = v___x_5828_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5845_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5845_, 0, v___x_5842_);
                    v___x_5844_ = v_reuseFailAlloc_5845_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5844_;
            }
            7 => {
                if v_isShared_5858_ == 0 {
                    v___x_5860_ = v___x_5857_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_a_5855_);
                    v___x_5860_ = v_reuseFailAlloc_5861_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5860_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___lam__1___boxed(
    mut v_a_5863_: *mut crate::leanh::LeanObject,
    mut v___y_5864_: *mut crate::leanh::LeanObject,
    mut v___f_5865_: *mut crate::leanh::LeanObject,
    mut v___y_5866_: *mut crate::leanh::LeanObject,
    mut v___y_5867_: *mut crate::leanh::LeanObject,
    mut v___y_5868_: *mut crate::leanh::LeanObject,
    mut v___y_5869_: *mut crate::leanh::LeanObject,
    mut v___y_5870_: *mut crate::leanh::LeanObject,
    mut v___y_5871_: *mut crate::leanh::LeanObject,
    mut v___y_5872_: *mut crate::leanh::LeanObject,
    mut v___y_5873_: *mut crate::leanh::LeanObject,
    mut v___y_5874_: *mut crate::leanh::LeanObject,
    mut v___y_5875_: *mut crate::leanh::LeanObject,
    mut v___y_5876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5877_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___lam__1(v_a_5863_, v___y_5864_, v___f_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_, v___y_5875_);
    crate::leanh::lean_dec(v___y_5875_);
    crate::leanh::lean_dec_ref(v___y_5874_);
    crate::leanh::lean_dec(v___y_5873_);
    crate::leanh::lean_dec_ref(v___y_5872_);
    crate::leanh::lean_dec(v___y_5871_);
    crate::leanh::lean_dec_ref(v___y_5870_);
    crate::leanh::lean_dec(v___y_5869_);
    crate::leanh::lean_dec_ref(v___y_5868_);
    crate::leanh::lean_dec(v___y_5867_);
    crate::leanh::lean_dec_ref(v___y_5866_);
    return v_res_5877_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg(
    mut v_upperBound_5884_: *mut crate::leanh::LeanObject,
    mut v___x_5885_: *mut crate::leanh::LeanObject,
    mut v_a_5886_: *mut crate::leanh::LeanObject,
    mut v_b_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
    mut v___y_5889_: *mut crate::leanh::LeanObject,
    mut v___y_5890_: *mut crate::leanh::LeanObject,
    mut v___y_5891_: *mut crate::leanh::LeanObject,
    mut v___y_5892_: *mut crate::leanh::LeanObject,
    mut v___y_5893_: *mut crate::leanh::LeanObject,
    mut v___y_5894_: *mut crate::leanh::LeanObject,
    mut v___y_5895_: *mut crate::leanh::LeanObject,
    mut v___y_5896_: *mut crate::leanh::LeanObject,
    mut v___y_5897_: *mut crate::leanh::LeanObject,
    mut v___y_5898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5906_: u8 = 0;
    let mut v_fst_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5911_: u8 = 0;
    let mut v_a_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5915_: u8 = 0;
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5925_: u8 = 0;
    let mut v_isSharedCheck_5926_: u8 = 0;
    let mut v_unused_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5931_: u8 = 0;
    let mut v_snd_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5935_: u8 = 0;
    let mut v_a_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5946_: u8 = 0;
    let mut v_unused_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5953_: u8 = 0;
    let mut v_isSharedCheck_5954_: u8 = 0;
    let mut v_a_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5958_: u8 = 0;
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5962_: u8 = 0;
    let mut v___x_5963_: u8 = 0;
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: u8 = 0;
    let mut v___f_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5963_ = lean_nat_dec_lt(v_a_5886_, v_upperBound_5884_);
                if v___x_5963_ == 0 {
                    crate::leanh::lean_dec(v_a_5886_);
                    v___x_5964_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5964_, 0, v_b_5887_);
                    v___x_5965_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5965_, 0, v___x_5964_);
                    crate::leanh::lean_ctor_set(v___x_5965_, 1, v___y_5889_);
                    v___x_5966_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5966_, 0, v___x_5965_);
                    return v___x_5966_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5887_);
                    v___x_5967_ = crate::leanh::lean_box(0);
                    v___x_5968_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___closed__0;
                    v___f_5969_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___closed__1;
                    v___x_5970_ = lean_array_fget_borrowed(v___x_5885_, v_a_5886_);
                    v___x_5971_ = (crate::leanh::lean_unbox(v___x_5970_) as u8);
                    if v___x_5971_ == 0 {
                        crate::leanh::lean_inc_ref(v___y_5888_);
                        crate::leanh::lean_inc(v_a_5886_);
                        v___f_5972_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___lam__1___boxed as *mut core::ffi::c_void, 14, 4);
                        crate::leanh::lean_closure_set(v___f_5972_, 0, v_a_5886_);
                        crate::leanh::lean_closure_set(v___f_5972_, 1, v___y_5889_);
                        crate::leanh::lean_closure_set(v___f_5972_, 2, v___f_5969_);
                        crate::leanh::lean_closure_set(v___f_5972_, 3, v___y_5888_);
                        v___y_5901_ = v___f_5972_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v___y_5888_);
                        v___x_5973_ = crate::leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 15, 5);
                        crate::leanh::lean_closure_set(v___x_5973_, 0, v___x_5968_);
                        crate::leanh::lean_closure_set(v___x_5973_, 1, v___x_5967_);
                        crate::leanh::lean_closure_set(v___x_5973_, 2, v___x_5967_);
                        crate::leanh::lean_closure_set(v___x_5973_, 3, v___y_5888_);
                        crate::leanh::lean_closure_set(v___x_5973_, 4, v___y_5889_);
                        v___y_5901_ = v___x_5973_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_5898_);
                crate::leanh::lean_inc_ref(v___y_5897_);
                crate::leanh::lean_inc(v___y_5896_);
                crate::leanh::lean_inc_ref(v___y_5895_);
                crate::leanh::lean_inc(v___y_5894_);
                crate::leanh::lean_inc_ref(v___y_5893_);
                crate::leanh::lean_inc(v___y_5892_);
                crate::leanh::lean_inc_ref(v___y_5891_);
                crate::leanh::lean_inc(v___y_5890_);
                v___x_5902_ = crate::leanh::lean_apply_10(
                    v___y_5901_,
                    v___y_5890_,
                    v___y_5891_,
                    v___y_5892_,
                    v___y_5893_,
                    v___y_5894_,
                    v___y_5895_,
                    v___y_5896_,
                    v___y_5897_,
                    v___y_5898_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5902_) == 0 {
                    v_a_5903_ = crate::leanh::lean_ctor_get(v___x_5902_, 0);
                    v_isSharedCheck_5954_ = (!crate::leanh::lean_is_exclusive(v___x_5902_)) as u8;
                    if v_isSharedCheck_5954_ == 0 {
                        v___x_5905_ = v___x_5902_;
                        v_isShared_5906_ = v_isSharedCheck_5954_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5903_);
                        crate::leanh::lean_dec(v___x_5902_);
                        v___x_5905_ = crate::leanh::lean_box(0);
                        v_isShared_5906_ = v_isSharedCheck_5954_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5886_);
                    v_a_5955_ = crate::leanh::lean_ctor_get(v___x_5902_, 0);
                    v_isSharedCheck_5962_ = (!crate::leanh::lean_is_exclusive(v___x_5902_)) as u8;
                    if v_isSharedCheck_5962_ == 0 {
                        v___x_5957_ = v___x_5902_;
                        v_isShared_5958_ = v_isSharedCheck_5962_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5955_);
                        crate::leanh::lean_dec(v___x_5902_);
                        v___x_5957_ = crate::leanh::lean_box(0);
                        v_isShared_5958_ = v_isSharedCheck_5962_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_5907_ = crate::leanh::lean_ctor_get(v_a_5903_, 0);
                crate::leanh::lean_inc(v_fst_5907_);
                if crate::leanh::lean_obj_tag(v_fst_5907_) == 0 {
                    crate::leanh::lean_dec(v_a_5886_);
                    v_snd_5908_ = crate::leanh::lean_ctor_get(v_a_5903_, 1);
                    v_isSharedCheck_5926_ = (!crate::leanh::lean_is_exclusive(v_a_5903_)) as u8;
                    if v_isSharedCheck_5926_ == 0 {
                        v_unused_5927_ = crate::leanh::lean_ctor_get(v_a_5903_, 0);
                        crate::leanh::lean_dec(v_unused_5927_);
                        v___x_5910_ = v_a_5903_;
                        v_isShared_5911_ = v_isSharedCheck_5926_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5908_);
                        crate::leanh::lean_dec(v_a_5903_);
                        v___x_5910_ = crate::leanh::lean_box(0);
                        v_isShared_5911_ = v_isSharedCheck_5926_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_5928_ = crate::leanh::lean_ctor_get(v_fst_5907_, 0);
                    v_isSharedCheck_5953_ = (!crate::leanh::lean_is_exclusive(v_fst_5907_)) as u8;
                    if v_isSharedCheck_5953_ == 0 {
                        v___x_5930_ = v_fst_5907_;
                        v_isShared_5931_ = v_isSharedCheck_5953_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5928_);
                        crate::leanh::lean_dec(v_fst_5907_);
                        v___x_5930_ = crate::leanh::lean_box(0);
                        v_isShared_5931_ = v_isSharedCheck_5953_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_a_5912_ = crate::leanh::lean_ctor_get(v_fst_5907_, 0);
                v_isSharedCheck_5925_ = (!crate::leanh::lean_is_exclusive(v_fst_5907_)) as u8;
                if v_isSharedCheck_5925_ == 0 {
                    v___x_5914_ = v_fst_5907_;
                    v_isShared_5915_ = v_isSharedCheck_5925_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5912_);
                    crate::leanh::lean_dec(v_fst_5907_);
                    v___x_5914_ = crate::leanh::lean_box(0);
                    v_isShared_5915_ = v_isSharedCheck_5925_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5915_ == 0 {
                    v___x_5917_ = v___x_5914_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5924_, 0, v_a_5912_);
                    v___x_5917_ = v_reuseFailAlloc_5924_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5910_, 0, v___x_5917_);
                    v___x_5919_ = v___x_5910_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5923_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5923_, 0, v___x_5917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5923_, 1, v_snd_5908_);
                    v___x_5919_ = v_reuseFailAlloc_5923_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5906_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5905_, 0, v___x_5919_);
                    v___x_5921_ = v___x_5905_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 0, v___x_5919_);
                    v___x_5921_ = v_reuseFailAlloc_5922_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5921_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_5928_) == 0 {
                    crate::leanh::lean_dec(v_a_5886_);
                    v_snd_5932_ = crate::leanh::lean_ctor_get(v_a_5903_, 1);
                    v_isSharedCheck_5946_ = (!crate::leanh::lean_is_exclusive(v_a_5903_)) as u8;
                    if v_isSharedCheck_5946_ == 0 {
                        v_unused_5947_ = crate::leanh::lean_ctor_get(v_a_5903_, 0);
                        crate::leanh::lean_dec(v_unused_5947_);
                        v___x_5934_ = v_a_5903_;
                        v_isShared_5935_ = v_isSharedCheck_5946_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5932_);
                        crate::leanh::lean_dec(v_a_5903_);
                        v___x_5934_ = crate::leanh::lean_box(0);
                        v_isShared_5935_ = v_isSharedCheck_5946_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5930_);
                    crate::leanh::lean_del_object(v___x_5905_);
                    v_snd_5948_ = crate::leanh::lean_ctor_get(v_a_5903_, 1);
                    crate::leanh::lean_inc(v_snd_5948_);
                    crate::leanh::lean_dec(v_a_5903_);
                    v_a_5949_ = crate::leanh::lean_ctor_get(v_a_5928_, 0);
                    crate::leanh::lean_inc(v_a_5949_);
                    crate::leanh::lean_dec_ref_known(v_a_5928_, 1);
                    v___x_5950_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5951_ = lean_nat_add(v_a_5886_, v___x_5950_);
                    crate::leanh::lean_dec(v_a_5886_);
                    v_a_5886_ = v___x_5951_;
                    v_b_5887_ = v_a_5949_;
                    v___y_5889_ = v_snd_5948_;
                    state = 0;
                    continue;
                }
            }
            9 => {
                v_a_5936_ = crate::leanh::lean_ctor_get(v_a_5928_, 0);
                crate::leanh::lean_inc(v_a_5936_);
                crate::leanh::lean_dec_ref_known(v_a_5928_, 1);
                if v_isShared_5931_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5930_, 0, v_a_5936_);
                    v___x_5938_ = v___x_5930_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5945_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5945_, 0, v_a_5936_);
                    v___x_5938_ = v_reuseFailAlloc_5945_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_5935_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5934_, 0, v___x_5938_);
                    v___x_5940_ = v___x_5934_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5944_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 0, v___x_5938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 1, v_snd_5932_);
                    v___x_5940_ = v_reuseFailAlloc_5944_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5906_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5905_, 0, v___x_5940_);
                    v___x_5942_ = v___x_5905_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5943_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5943_, 0, v___x_5940_);
                    v___x_5942_ = v_reuseFailAlloc_5943_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5942_;
            }
            13 => {
                if v_isShared_5958_ == 0 {
                    v___x_5960_ = v___x_5957_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_a_5955_);
                    v___x_5960_ = v_reuseFailAlloc_5961_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5960_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_upperBound_5974_: *mut crate::leanh::LeanObject,
    mut v___x_5975_: *mut crate::leanh::LeanObject,
    mut v_a_5976_: *mut crate::leanh::LeanObject,
    mut v_b_5977_: *mut crate::leanh::LeanObject,
    mut v___y_5978_: *mut crate::leanh::LeanObject,
    mut v___y_5979_: *mut crate::leanh::LeanObject,
    mut v___y_5980_: *mut crate::leanh::LeanObject,
    mut v___y_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
    mut v___y_5983_: *mut crate::leanh::LeanObject,
    mut v___y_5984_: *mut crate::leanh::LeanObject,
    mut v___y_5985_: *mut crate::leanh::LeanObject,
    mut v___y_5986_: *mut crate::leanh::LeanObject,
    mut v___y_5987_: *mut crate::leanh::LeanObject,
    mut v___y_5988_: *mut crate::leanh::LeanObject,
    mut v___y_5989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5990_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg(v_upperBound_5974_, v___x_5975_, v_a_5976_, v_b_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_, v___y_5987_, v___y_5988_);
    crate::leanh::lean_dec(v___y_5988_);
    crate::leanh::lean_dec_ref(v___y_5987_);
    crate::leanh::lean_dec(v___y_5986_);
    crate::leanh::lean_dec_ref(v___y_5985_);
    crate::leanh::lean_dec(v___y_5984_);
    crate::leanh::lean_dec_ref(v___y_5983_);
    crate::leanh::lean_dec(v___y_5982_);
    crate::leanh::lean_dec_ref(v___y_5981_);
    crate::leanh::lean_dec(v___y_5980_);
    crate::leanh::lean_dec_ref(v___y_5978_);
    crate::leanh::lean_dec_ref(v___x_5975_);
    crate::leanh::lean_dec(v_upperBound_5974_);
    return v_res_5990_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2(
    mut v_a_5991_: *mut crate::leanh::LeanObject,
    mut v_a_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
    mut v___y_5995_: *mut crate::leanh::LeanObject,
    mut v___y_5996_: *mut crate::leanh::LeanObject,
    mut v___y_5997_: *mut crate::leanh::LeanObject,
    mut v___y_5998_: *mut crate::leanh::LeanObject,
    mut v___y_5999_: *mut crate::leanh::LeanObject,
    mut v___y_6000_: *mut crate::leanh::LeanObject,
    mut v___y_6001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_initialMask_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6011_: u8 = 0;
    let mut v_fst_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6016_: u8 = 0;
    let mut v_a_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6020_: u8 = 0;
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6030_: u8 = 0;
    let mut v_isSharedCheck_6031_: u8 = 0;
    let mut v_unused_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6036_: u8 = 0;
    let mut v_fst_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6040_: u8 = 0;
    let mut v_snd_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6060_: u8 = 0;
    let mut v_unused_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6062_: u8 = 0;
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut v_a_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6067_: u8 = 0;
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_initialMask_6003_ = crate::leanh::lean_ctor_get(v_a_5991_, 0);
                v___x_6004_ = lean_array_get_size(v_initialMask_6003_);
                v___x_6005_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6006_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg___closed__0;
                v___x_6007_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg(v___x_6004_, v_initialMask_6003_, v___x_6005_, v___x_6006_, v_a_5991_, v_a_5992_, v___y_5993_, v___y_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_);
                if crate::leanh::lean_obj_tag(v___x_6007_) == 0 {
                    v_a_6008_ = crate::leanh::lean_ctor_get(v___x_6007_, 0);
                    v_isSharedCheck_6063_ = (!crate::leanh::lean_is_exclusive(v___x_6007_)) as u8;
                    if v_isSharedCheck_6063_ == 0 {
                        v___x_6010_ = v___x_6007_;
                        v_isShared_6011_ = v_isSharedCheck_6063_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6008_);
                        crate::leanh::lean_dec(v___x_6007_);
                        v___x_6010_ = crate::leanh::lean_box(0);
                        v_isShared_6011_ = v_isSharedCheck_6063_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6064_ = crate::leanh::lean_ctor_get(v___x_6007_, 0);
                    v_isSharedCheck_6071_ = (!crate::leanh::lean_is_exclusive(v___x_6007_)) as u8;
                    if v_isSharedCheck_6071_ == 0 {
                        v___x_6066_ = v___x_6007_;
                        v_isShared_6067_ = v_isSharedCheck_6071_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6064_);
                        crate::leanh::lean_dec(v___x_6007_);
                        v___x_6066_ = crate::leanh::lean_box(0);
                        v_isShared_6067_ = v_isSharedCheck_6071_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6012_ = crate::leanh::lean_ctor_get(v_a_6008_, 0);
                crate::leanh::lean_inc(v_fst_6012_);
                if crate::leanh::lean_obj_tag(v_fst_6012_) == 0 {
                    v_snd_6013_ = crate::leanh::lean_ctor_get(v_a_6008_, 1);
                    v_isSharedCheck_6031_ = (!crate::leanh::lean_is_exclusive(v_a_6008_)) as u8;
                    if v_isSharedCheck_6031_ == 0 {
                        v_unused_6032_ = crate::leanh::lean_ctor_get(v_a_6008_, 0);
                        crate::leanh::lean_dec(v_unused_6032_);
                        v___x_6015_ = v_a_6008_;
                        v_isShared_6016_ = v_isSharedCheck_6031_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6013_);
                        crate::leanh::lean_dec(v_a_6008_);
                        v___x_6015_ = crate::leanh::lean_box(0);
                        v_isShared_6016_ = v_isSharedCheck_6031_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6033_ = crate::leanh::lean_ctor_get(v_fst_6012_, 0);
                    v_isSharedCheck_6062_ = (!crate::leanh::lean_is_exclusive(v_fst_6012_)) as u8;
                    if v_isSharedCheck_6062_ == 0 {
                        v___x_6035_ = v_fst_6012_;
                        v_isShared_6036_ = v_isSharedCheck_6062_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6033_);
                        crate::leanh::lean_dec(v_fst_6012_);
                        v___x_6035_ = crate::leanh::lean_box(0);
                        v_isShared_6036_ = v_isSharedCheck_6062_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_a_6017_ = crate::leanh::lean_ctor_get(v_fst_6012_, 0);
                v_isSharedCheck_6030_ = (!crate::leanh::lean_is_exclusive(v_fst_6012_)) as u8;
                if v_isSharedCheck_6030_ == 0 {
                    v___x_6019_ = v_fst_6012_;
                    v_isShared_6020_ = v_isSharedCheck_6030_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6017_);
                    crate::leanh::lean_dec(v_fst_6012_);
                    v___x_6019_ = crate::leanh::lean_box(0);
                    v_isShared_6020_ = v_isSharedCheck_6030_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6020_ == 0 {
                    v___x_6022_ = v___x_6019_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6029_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 0, v_a_6017_);
                    v___x_6022_ = v_reuseFailAlloc_6029_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6015_, 0, v___x_6022_);
                    v___x_6024_ = v___x_6015_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6028_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6028_, 0, v___x_6022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6028_, 1, v_snd_6013_);
                    v___x_6024_ = v_reuseFailAlloc_6028_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6011_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6010_, 0, v___x_6024_);
                    v___x_6026_ = v___x_6010_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6027_, 0, v___x_6024_);
                    v___x_6026_ = v_reuseFailAlloc_6027_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6026_;
            }
            7 => {
                v_fst_6037_ = crate::leanh::lean_ctor_get(v_a_6033_, 0);
                v_isSharedCheck_6060_ = (!crate::leanh::lean_is_exclusive(v_a_6033_)) as u8;
                if v_isSharedCheck_6060_ == 0 {
                    v_unused_6061_ = crate::leanh::lean_ctor_get(v_a_6033_, 1);
                    crate::leanh::lean_dec(v_unused_6061_);
                    v___x_6039_ = v_a_6033_;
                    v_isShared_6040_ = v_isSharedCheck_6060_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_6037_);
                    crate::leanh::lean_dec(v_a_6033_);
                    v___x_6039_ = crate::leanh::lean_box(0);
                    v_isShared_6040_ = v_isSharedCheck_6060_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_fst_6037_) == 0 {
                    crate::leanh::lean_del_object(v___x_6035_);
                    v_snd_6041_ = crate::leanh::lean_ctor_get(v_a_6008_, 1);
                    crate::leanh::lean_inc(v_snd_6041_);
                    crate::leanh::lean_dec(v_a_6008_);
                    v___x_6042_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
                    if v_isShared_6040_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6039_, 1, v_snd_6041_);
                        crate::leanh::lean_ctor_set(v___x_6039_, 0, v___x_6042_);
                        v___x_6044_ = v___x_6039_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_6048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6048_, 0, v___x_6042_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6048_, 1, v_snd_6041_);
                        v___x_6044_ = v_reuseFailAlloc_6048_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_snd_6049_ = crate::leanh::lean_ctor_get(v_a_6008_, 1);
                    crate::leanh::lean_inc(v_snd_6049_);
                    crate::leanh::lean_dec(v_a_6008_);
                    v_val_6050_ = crate::leanh::lean_ctor_get(v_fst_6037_, 0);
                    crate::leanh::lean_inc(v_val_6050_);
                    crate::leanh::lean_dec_ref_known(v_fst_6037_, 1);
                    if v_isShared_6036_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6035_, 0, v_val_6050_);
                        v___x_6052_ = v___x_6035_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_6059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6059_, 0, v_val_6050_);
                        v___x_6052_ = v_reuseFailAlloc_6059_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_6011_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6010_, 0, v___x_6044_);
                    v___x_6046_ = v___x_6010_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6047_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6047_, 0, v___x_6044_);
                    v___x_6046_ = v_reuseFailAlloc_6047_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6046_;
            }
            11 => {
                if v_isShared_6040_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6039_, 1, v_snd_6049_);
                    crate::leanh::lean_ctor_set(v___x_6039_, 0, v___x_6052_);
                    v___x_6054_ = v___x_6039_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6058_, 0, v___x_6052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6058_, 1, v_snd_6049_);
                    v___x_6054_ = v_reuseFailAlloc_6058_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_6011_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6010_, 0, v___x_6054_);
                    v___x_6056_ = v___x_6010_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6057_, 0, v___x_6054_);
                    v___x_6056_ = v_reuseFailAlloc_6057_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6056_;
            }
            14 => {
                if v_isShared_6067_ == 0 {
                    v___x_6069_ = v___x_6066_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6070_, 0, v_a_6064_);
                    v___x_6069_ = v_reuseFailAlloc_6070_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2___boxed(
    mut v_a_6072_: *mut crate::leanh::LeanObject,
    mut v_a_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
    mut v___y_6077_: *mut crate::leanh::LeanObject,
    mut v___y_6078_: *mut crate::leanh::LeanObject,
    mut v___y_6079_: *mut crate::leanh::LeanObject,
    mut v___y_6080_: *mut crate::leanh::LeanObject,
    mut v___y_6081_: *mut crate::leanh::LeanObject,
    mut v___y_6082_: *mut crate::leanh::LeanObject,
    mut v___y_6083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6084_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2(v_a_6072_, v_a_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_, v___y_6081_, v___y_6082_);
    crate::leanh::lean_dec(v___y_6082_);
    crate::leanh::lean_dec_ref(v___y_6081_);
    crate::leanh::lean_dec(v___y_6080_);
    crate::leanh::lean_dec_ref(v___y_6079_);
    crate::leanh::lean_dec(v___y_6078_);
    crate::leanh::lean_dec_ref(v___y_6077_);
    crate::leanh::lean_dec(v___y_6076_);
    crate::leanh::lean_dec_ref(v___y_6075_);
    crate::leanh::lean_dec(v___y_6074_);
    crate::leanh::lean_dec_ref(v_a_6072_);
    return v_res_6084_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__8___redArg(
    mut v_i_6085_: *mut crate::leanh::LeanObject,
    mut v_a_6086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cur_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_6091_: u8 = 0;
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6094_: u8 = 0;
    let mut v___x_6095_: u8 = 0;
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cur_6088_ = crate::leanh::lean_ctor_get(v_a_6086_, 0);
                v_added_6089_ = crate::leanh::lean_ctor_get(v_a_6086_, 1);
                v_numCalls_6090_ = crate::leanh::lean_ctor_get(v_a_6086_, 2);
                v_found_6091_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6086_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_6104_ = (!crate::leanh::lean_is_exclusive(v_a_6086_)) as u8;
                if v_isSharedCheck_6104_ == 0 {
                    v___x_6093_ = v_a_6086_;
                    v_isShared_6094_ = v_isSharedCheck_6104_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numCalls_6090_);
                    crate::leanh::lean_inc(v_added_6089_);
                    crate::leanh::lean_inc(v_cur_6088_);
                    crate::leanh::lean_dec(v_a_6086_);
                    v___x_6093_ = crate::leanh::lean_box(0);
                    v_isShared_6094_ = v_isSharedCheck_6104_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6095_ = 1;
                v___x_6096_ = crate::leanh::lean_box((v___x_6095_) as usize);
                v___x_6097_ = lean_array_set(v_cur_6088_, v_i_6085_, v___x_6096_);
                if v_isShared_6094_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6093_, 0, v___x_6097_);
                    v___x_6099_ = v___x_6093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6103_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6103_, 0, v___x_6097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6103_, 1, v_added_6089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6103_, 2, v_numCalls_6090_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6103_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_found_6091_,
                    );
                    v___x_6099_ = v_reuseFailAlloc_6103_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6100_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
                v___x_6101_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6101_, 0, v___x_6100_);
                crate::leanh::lean_ctor_set(v___x_6101_, 1, v___x_6099_);
                v___x_6102_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6102_, 0, v___x_6101_);
                return v___x_6102_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_i_6105_: *mut crate::leanh::LeanObject,
    mut v_a_6106_: *mut crate::leanh::LeanObject,
    mut v___y_6107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6108_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__8___redArg(v_i_6105_, v_a_6106_);
    crate::leanh::lean_dec(v_i_6105_);
    return v_res_6108_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg___lam__0(
    mut v_____x_6109_: *mut crate::leanh::LeanObject,
    mut v___y_6110_: *mut crate::leanh::LeanObject,
    mut v___y_6111_: *mut crate::leanh::LeanObject,
    mut v___y_6112_: *mut crate::leanh::LeanObject,
    mut v___y_6113_: *mut crate::leanh::LeanObject,
    mut v___y_6114_: *mut crate::leanh::LeanObject,
    mut v___y_6115_: *mut crate::leanh::LeanObject,
    mut v___y_6116_: *mut crate::leanh::LeanObject,
    mut v___y_6117_: *mut crate::leanh::LeanObject,
    mut v___y_6118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6124_: u8 = 0;
    let mut v_a_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6128_: u8 = 0;
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6136_: u8 = 0;
    let mut v_isSharedCheck_6137_: u8 = 0;
    let mut v_unused_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6142_: u8 = 0;
    let mut v_snd_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6146_: u8 = 0;
    let mut v_a_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6150_: u8 = 0;
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6161_: u8 = 0;
    let mut v_isSharedCheck_6162_: u8 = 0;
    let mut v_unused_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6167_: u8 = 0;
    let mut v_a_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6171_: u8 = 0;
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6182_: u8 = 0;
    let mut v_isSharedCheck_6183_: u8 = 0;
    let mut v_unused_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6185_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_6120_ = crate::leanh::lean_ctor_get(v_____x_6109_, 0);
                crate::leanh::lean_inc(v_fst_6120_);
                if crate::leanh::lean_obj_tag(v_fst_6120_) == 0 {
                    v_snd_6121_ = crate::leanh::lean_ctor_get(v_____x_6109_, 1);
                    v_isSharedCheck_6137_ = (!crate::leanh::lean_is_exclusive(v_____x_6109_)) as u8;
                    if v_isSharedCheck_6137_ == 0 {
                        v_unused_6138_ = crate::leanh::lean_ctor_get(v_____x_6109_, 0);
                        crate::leanh::lean_dec(v_unused_6138_);
                        v___x_6123_ = v_____x_6109_;
                        v_isShared_6124_ = v_isSharedCheck_6137_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6121_);
                        crate::leanh::lean_dec(v_____x_6109_);
                        v___x_6123_ = crate::leanh::lean_box(0);
                        v_isShared_6124_ = v_isSharedCheck_6137_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6139_ = crate::leanh::lean_ctor_get(v_fst_6120_, 0);
                    v_isSharedCheck_6185_ = (!crate::leanh::lean_is_exclusive(v_fst_6120_)) as u8;
                    if v_isSharedCheck_6185_ == 0 {
                        v___x_6141_ = v_fst_6120_;
                        v_isShared_6142_ = v_isSharedCheck_6185_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6139_);
                        crate::leanh::lean_dec(v_fst_6120_);
                        v___x_6141_ = crate::leanh::lean_box(0);
                        v_isShared_6142_ = v_isSharedCheck_6185_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6125_ = crate::leanh::lean_ctor_get(v_fst_6120_, 0);
                v_isSharedCheck_6136_ = (!crate::leanh::lean_is_exclusive(v_fst_6120_)) as u8;
                if v_isSharedCheck_6136_ == 0 {
                    v___x_6127_ = v_fst_6120_;
                    v_isShared_6128_ = v_isSharedCheck_6136_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6125_);
                    crate::leanh::lean_dec(v_fst_6120_);
                    v___x_6127_ = crate::leanh::lean_box(0);
                    v_isShared_6128_ = v_isSharedCheck_6136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6128_ == 0 {
                    v___x_6130_ = v___x_6127_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6135_, 0, v_a_6125_);
                    v___x_6130_ = v_reuseFailAlloc_6135_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6124_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6123_, 0, v___x_6130_);
                    v___x_6132_ = v___x_6123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6134_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6134_, 0, v___x_6130_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6134_, 1, v_snd_6121_);
                    v___x_6132_ = v_reuseFailAlloc_6134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6133_, 0, v___x_6132_);
                return v___x_6133_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_6139_) == 0 {
                    v_snd_6143_ = crate::leanh::lean_ctor_get(v_____x_6109_, 1);
                    v_isSharedCheck_6162_ = (!crate::leanh::lean_is_exclusive(v_____x_6109_)) as u8;
                    if v_isSharedCheck_6162_ == 0 {
                        v_unused_6163_ = crate::leanh::lean_ctor_get(v_____x_6109_, 0);
                        crate::leanh::lean_dec(v_unused_6163_);
                        v___x_6145_ = v_____x_6109_;
                        v_isShared_6146_ = v_isSharedCheck_6162_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6143_);
                        crate::leanh::lean_dec(v_____x_6109_);
                        v___x_6145_ = crate::leanh::lean_box(0);
                        v_isShared_6146_ = v_isSharedCheck_6162_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_snd_6164_ = crate::leanh::lean_ctor_get(v_____x_6109_, 1);
                    v_isSharedCheck_6183_ = (!crate::leanh::lean_is_exclusive(v_____x_6109_)) as u8;
                    if v_isSharedCheck_6183_ == 0 {
                        v_unused_6184_ = crate::leanh::lean_ctor_get(v_____x_6109_, 0);
                        crate::leanh::lean_dec(v_unused_6184_);
                        v___x_6166_ = v_____x_6109_;
                        v_isShared_6167_ = v_isSharedCheck_6183_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6164_);
                        crate::leanh::lean_dec(v_____x_6109_);
                        v___x_6166_ = crate::leanh::lean_box(0);
                        v_isShared_6167_ = v_isSharedCheck_6183_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                v_a_6147_ = crate::leanh::lean_ctor_get(v_a_6139_, 0);
                v_isSharedCheck_6161_ = (!crate::leanh::lean_is_exclusive(v_a_6139_)) as u8;
                if v_isSharedCheck_6161_ == 0 {
                    v___x_6149_ = v_a_6139_;
                    v_isShared_6150_ = v_isSharedCheck_6161_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6147_);
                    crate::leanh::lean_dec(v_a_6139_);
                    v___x_6149_ = crate::leanh::lean_box(0);
                    v_isShared_6150_ = v_isSharedCheck_6161_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6150_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6149_, 1);
                    v___x_6152_ = v___x_6149_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6160_, 0, v_a_6147_);
                    v___x_6152_ = v_reuseFailAlloc_6160_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_6142_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6141_, 0, v___x_6152_);
                    v___x_6154_ = v___x_6141_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6159_, 0, v___x_6152_);
                    v___x_6154_ = v_reuseFailAlloc_6159_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_6146_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6145_, 0, v___x_6154_);
                    v___x_6156_ = v___x_6145_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6158_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6158_, 0, v___x_6154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6158_, 1, v_snd_6143_);
                    v___x_6156_ = v_reuseFailAlloc_6158_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_6157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6157_, 0, v___x_6156_);
                return v___x_6157_;
            }
            11 => {
                v_a_6168_ = crate::leanh::lean_ctor_get(v_a_6139_, 0);
                v_isSharedCheck_6182_ = (!crate::leanh::lean_is_exclusive(v_a_6139_)) as u8;
                if v_isSharedCheck_6182_ == 0 {
                    v___x_6170_ = v_a_6139_;
                    v_isShared_6171_ = v_isSharedCheck_6182_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6168_);
                    crate::leanh::lean_dec(v_a_6139_);
                    v___x_6170_ = crate::leanh::lean_box(0);
                    v_isShared_6171_ = v_isSharedCheck_6182_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_6171_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6170_, 0);
                    v___x_6173_ = v___x_6170_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_a_6168_);
                    v___x_6173_ = v_reuseFailAlloc_6181_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_6142_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6141_, 0, v___x_6173_);
                    v___x_6175_ = v___x_6141_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6180_, 0, v___x_6173_);
                    v___x_6175_ = v_reuseFailAlloc_6180_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_6167_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6166_, 0, v___x_6175_);
                    v___x_6177_ = v___x_6166_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6179_, 0, v___x_6175_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6179_, 1, v_snd_6164_);
                    v___x_6177_ = v_reuseFailAlloc_6179_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_6178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6178_, 0, v___x_6177_);
                return v___x_6178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg___lam__0___boxed(
    mut v_____x_6186_: *mut crate::leanh::LeanObject,
    mut v___y_6187_: *mut crate::leanh::LeanObject,
    mut v___y_6188_: *mut crate::leanh::LeanObject,
    mut v___y_6189_: *mut crate::leanh::LeanObject,
    mut v___y_6190_: *mut crate::leanh::LeanObject,
    mut v___y_6191_: *mut crate::leanh::LeanObject,
    mut v___y_6192_: *mut crate::leanh::LeanObject,
    mut v___y_6193_: *mut crate::leanh::LeanObject,
    mut v___y_6194_: *mut crate::leanh::LeanObject,
    mut v___y_6195_: *mut crate::leanh::LeanObject,
    mut v___y_6196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6197_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg___lam__0(v_____x_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, v___y_6195_);
    crate::leanh::lean_dec(v___y_6195_);
    crate::leanh::lean_dec_ref(v___y_6194_);
    crate::leanh::lean_dec(v___y_6193_);
    crate::leanh::lean_dec_ref(v___y_6192_);
    crate::leanh::lean_dec(v___y_6191_);
    crate::leanh::lean_dec_ref(v___y_6190_);
    crate::leanh::lean_dec(v___y_6189_);
    crate::leanh::lean_dec_ref(v___y_6188_);
    crate::leanh::lean_dec(v___y_6187_);
    return v_res_6197_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__7___redArg(
    mut v_i_6198_: *mut crate::leanh::LeanObject,
    mut v_a_6199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cur_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_6204_: u8 = 0;
    let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6207_: u8 = 0;
    let mut v___x_6208_: u8 = 0;
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_cur_6201_ = crate::leanh::lean_ctor_get(v_a_6199_, 0);
                v_added_6202_ = crate::leanh::lean_ctor_get(v_a_6199_, 1);
                v_numCalls_6203_ = crate::leanh::lean_ctor_get(v_a_6199_, 2);
                v_found_6204_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6199_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_6217_ = (!crate::leanh::lean_is_exclusive(v_a_6199_)) as u8;
                if v_isSharedCheck_6217_ == 0 {
                    v___x_6206_ = v_a_6199_;
                    v_isShared_6207_ = v_isSharedCheck_6217_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_numCalls_6203_);
                    crate::leanh::lean_inc(v_added_6202_);
                    crate::leanh::lean_inc(v_cur_6201_);
                    crate::leanh::lean_dec(v_a_6199_);
                    v___x_6206_ = crate::leanh::lean_box(0);
                    v_isShared_6207_ = v_isSharedCheck_6217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6208_ = 0;
                v___x_6209_ = crate::leanh::lean_box((v___x_6208_) as usize);
                v___x_6210_ = lean_array_set(v_cur_6201_, v_i_6198_, v___x_6209_);
                if v_isShared_6207_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6206_, 0, v___x_6210_);
                    v___x_6212_ = v___x_6206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6216_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6216_, 0, v___x_6210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6216_, 1, v_added_6202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6216_, 2, v_numCalls_6203_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6216_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_found_6204_,
                    );
                    v___x_6212_ = v_reuseFailAlloc_6216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6213_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
                v___x_6214_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6214_, 0, v___x_6213_);
                crate::leanh::lean_ctor_set(v___x_6214_, 1, v___x_6212_);
                v___x_6215_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6215_, 0, v___x_6214_);
                return v___x_6215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_i_6218_: *mut crate::leanh::LeanObject,
    mut v_a_6219_: *mut crate::leanh::LeanObject,
    mut v___y_6220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6221_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__7___redArg(v_i_6218_, v_a_6219_);
    crate::leanh::lean_dec(v_i_6218_);
    return v_res_6221_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg(
    mut v_a_6222_: *mut crate::leanh::LeanObject,
    mut v___y_6223_: *mut crate::leanh::LeanObject,
    mut v___y_6224_: *mut crate::leanh::LeanObject,
    mut v___y_6225_: *mut crate::leanh::LeanObject,
    mut v___y_6226_: *mut crate::leanh::LeanObject,
    mut v___y_6227_: *mut crate::leanh::LeanObject,
    mut v___y_6228_: *mut crate::leanh::LeanObject,
    mut v___y_6229_: *mut crate::leanh::LeanObject,
    mut v___y_6230_: *mut crate::leanh::LeanObject,
    mut v___y_6231_: *mut crate::leanh::LeanObject,
    mut v___y_6232_: *mut crate::leanh::LeanObject,
    mut v___y_6233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6246_: u8 = 0;
    let mut v_fst_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6251_: u8 = 0;
    let mut v_a_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6255_: u8 = 0;
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6265_: u8 = 0;
    let mut v_isSharedCheck_6266_: u8 = 0;
    let mut v_unused_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6274_: u8 = 0;
    let mut v_a_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6278_: u8 = 0;
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6282_: u8 = 0;
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: u8 = 0;
    let mut v_added_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6295_: u8 = 0;
    let mut v_a_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6299_: u8 = 0;
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6307_: u8 = 0;
    let mut v_isSharedCheck_6308_: u8 = 0;
    let mut v_unused_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6317_: u8 = 0;
    let mut v_a_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6321_: u8 = 0;
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6329_: u8 = 0;
    let mut v_isSharedCheck_6330_: u8 = 0;
    let mut v_unused_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6335_: u8 = 0;
    let mut v___x_6336_: u8 = 0;
    let mut v_snd_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6344_: u8 = 0;
    let mut v_a_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6348_: u8 = 0;
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6356_: u8 = 0;
    let mut v_isSharedCheck_6357_: u8 = 0;
    let mut v_unused_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6362_: u8 = 0;
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6374_: u8 = 0;
    let mut v_unused_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6376_: u8 = 0;
    let mut v_unused_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6381_: u8 = 0;
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6385_: u8 = 0;
    let mut v_snd_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6389_: u8 = 0;
    let mut v___x_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6398_: u8 = 0;
    let mut v_unused_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6400_: u8 = 0;
    let mut v_a_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6404_: u8 = 0;
    let mut v___x_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6408_: u8 = 0;
    let mut v_a_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6412_: u8 = 0;
    let mut v___x_6414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6283_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6284_ = lean_nat_dec_lt(v___x_6283_, v_a_6222_);
                if v___x_6284_ == 0 {
                    v_val_6236_ = v_a_6222_;
                    v_snd_6237_ = v___y_6224_;
                    state = 1;
                    continue;
                } else {
                    v_added_6285_ = crate::leanh::lean_ctor_get(v___y_6224_, 1);
                    v___x_6286_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6287_ = lean_nat_sub(v_a_6222_, v___x_6286_);
                    crate::leanh::lean_dec(v_a_6222_);
                    v___x_6288_ = lean_array_get(v___x_6283_, v_added_6285_, v___x_6287_);
                    v___x_6289_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__7___redArg(v___x_6288_, v___y_6224_);
                    if crate::leanh::lean_obj_tag(v___x_6289_) == 0 {
                        v_a_6290_ = crate::leanh::lean_ctor_get(v___x_6289_, 0);
                        crate::leanh::lean_inc(v_a_6290_);
                        crate::leanh::lean_dec_ref_known(v___x_6289_, 1);
                        v_fst_6291_ = crate::leanh::lean_ctor_get(v_a_6290_, 0);
                        crate::leanh::lean_inc(v_fst_6291_);
                        if crate::leanh::lean_obj_tag(v_fst_6291_) == 0 {
                            crate::leanh::lean_dec(v___x_6288_);
                            crate::leanh::lean_dec(v___x_6287_);
                            v_snd_6292_ = crate::leanh::lean_ctor_get(v_a_6290_, 1);
                            v_isSharedCheck_6308_ =
                                (!crate::leanh::lean_is_exclusive(v_a_6290_)) as u8;
                            if v_isSharedCheck_6308_ == 0 {
                                v_unused_6309_ = crate::leanh::lean_ctor_get(v_a_6290_, 0);
                                crate::leanh::lean_dec(v_unused_6309_);
                                v___x_6294_ = v_a_6290_;
                                v_isShared_6295_ = v_isSharedCheck_6308_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_6292_);
                                crate::leanh::lean_dec(v_a_6290_);
                                v___x_6294_ = crate::leanh::lean_box(0);
                                v_isShared_6295_ = v_isSharedCheck_6308_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_fst_6291_, 1);
                            v_snd_6310_ = crate::leanh::lean_ctor_get(v_a_6290_, 1);
                            crate::leanh::lean_inc(v_snd_6310_);
                            crate::leanh::lean_dec(v_a_6290_);
                            v___x_6311_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3(v___y_6223_, v_snd_6310_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
                            if crate::leanh::lean_obj_tag(v___x_6311_) == 0 {
                                v_a_6312_ = crate::leanh::lean_ctor_get(v___x_6311_, 0);
                                crate::leanh::lean_inc(v_a_6312_);
                                crate::leanh::lean_dec_ref_known(v___x_6311_, 1);
                                v_fst_6313_ = crate::leanh::lean_ctor_get(v_a_6312_, 0);
                                crate::leanh::lean_inc(v_fst_6313_);
                                if crate::leanh::lean_obj_tag(v_fst_6313_) == 0 {
                                    crate::leanh::lean_dec(v___x_6288_);
                                    crate::leanh::lean_dec(v___x_6287_);
                                    v_snd_6314_ = crate::leanh::lean_ctor_get(v_a_6312_, 1);
                                    v_isSharedCheck_6330_ =
                                        (!crate::leanh::lean_is_exclusive(v_a_6312_)) as u8;
                                    if v_isSharedCheck_6330_ == 0 {
                                        v_unused_6331_ = crate::leanh::lean_ctor_get(v_a_6312_, 0);
                                        crate::leanh::lean_dec(v_unused_6331_);
                                        v___x_6316_ = v_a_6312_;
                                        v_isShared_6317_ = v_isSharedCheck_6330_;
                                        state = 15;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_snd_6314_);
                                        crate::leanh::lean_dec(v_a_6312_);
                                        v___x_6316_ = crate::leanh::lean_box(0);
                                        v_isShared_6317_ = v_isSharedCheck_6330_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    v_a_6332_ = crate::leanh::lean_ctor_get(v_fst_6313_, 0);
                                    v_isSharedCheck_6400_ =
                                        (!crate::leanh::lean_is_exclusive(v_fst_6313_)) as u8;
                                    if v_isSharedCheck_6400_ == 0 {
                                        v___x_6334_ = v_fst_6313_;
                                        v_isShared_6335_ = v_isSharedCheck_6400_;
                                        state = 19;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6332_);
                                        crate::leanh::lean_dec(v_fst_6313_);
                                        v___x_6334_ = crate::leanh::lean_box(0);
                                        v_isShared_6335_ = v_isSharedCheck_6400_;
                                        state = 19;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_6288_);
                                crate::leanh::lean_dec(v___x_6287_);
                                v_a_6401_ = crate::leanh::lean_ctor_get(v___x_6311_, 0);
                                v_isSharedCheck_6408_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6311_)) as u8;
                                if v_isSharedCheck_6408_ == 0 {
                                    v___x_6403_ = v___x_6311_;
                                    v_isShared_6404_ = v_isSharedCheck_6408_;
                                    state = 33;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6401_);
                                    crate::leanh::lean_dec(v___x_6311_);
                                    v___x_6403_ = crate::leanh::lean_box(0);
                                    v_isShared_6404_ = v_isSharedCheck_6408_;
                                    state = 33;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6288_);
                        crate::leanh::lean_dec(v___x_6287_);
                        v_a_6409_ = crate::leanh::lean_ctor_get(v___x_6289_, 0);
                        v_isSharedCheck_6416_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6289_)) as u8;
                        if v_isSharedCheck_6416_ == 0 {
                            v___x_6411_ = v___x_6289_;
                            v_isShared_6412_ = v_isSharedCheck_6416_;
                            state = 35;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6409_);
                            crate::leanh::lean_dec(v___x_6289_);
                            v___x_6411_ = crate::leanh::lean_box(0);
                            v_isShared_6412_ = v_isSharedCheck_6416_;
                            state = 35;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6238_, 0, v_val_6236_);
                v___x_6239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6239_, 0, v___x_6238_);
                crate::leanh::lean_ctor_set(v___x_6239_, 1, v_snd_6237_);
                v___x_6240_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6240_, 0, v___x_6239_);
                return v___x_6240_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_6242_) == 0 {
                    v_a_6243_ = crate::leanh::lean_ctor_get(v___y_6242_, 0);
                    v_isSharedCheck_6274_ = (!crate::leanh::lean_is_exclusive(v___y_6242_)) as u8;
                    if v_isSharedCheck_6274_ == 0 {
                        v___x_6245_ = v___y_6242_;
                        v_isShared_6246_ = v_isSharedCheck_6274_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6243_);
                        crate::leanh::lean_dec(v___y_6242_);
                        v___x_6245_ = crate::leanh::lean_box(0);
                        v_isShared_6246_ = v_isSharedCheck_6274_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_6275_ = crate::leanh::lean_ctor_get(v___y_6242_, 0);
                    v_isSharedCheck_6282_ = (!crate::leanh::lean_is_exclusive(v___y_6242_)) as u8;
                    if v_isSharedCheck_6282_ == 0 {
                        v___x_6277_ = v___y_6242_;
                        v_isShared_6278_ = v_isSharedCheck_6282_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6275_);
                        crate::leanh::lean_dec(v___y_6242_);
                        v___x_6277_ = crate::leanh::lean_box(0);
                        v_isShared_6278_ = v_isSharedCheck_6282_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_6247_ = crate::leanh::lean_ctor_get(v_a_6243_, 0);
                crate::leanh::lean_inc(v_fst_6247_);
                if crate::leanh::lean_obj_tag(v_fst_6247_) == 0 {
                    v_snd_6248_ = crate::leanh::lean_ctor_get(v_a_6243_, 1);
                    v_isSharedCheck_6266_ = (!crate::leanh::lean_is_exclusive(v_a_6243_)) as u8;
                    if v_isSharedCheck_6266_ == 0 {
                        v_unused_6267_ = crate::leanh::lean_ctor_get(v_a_6243_, 0);
                        crate::leanh::lean_dec(v_unused_6267_);
                        v___x_6250_ = v_a_6243_;
                        v_isShared_6251_ = v_isSharedCheck_6266_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6248_);
                        crate::leanh::lean_dec(v_a_6243_);
                        v___x_6250_ = crate::leanh::lean_box(0);
                        v_isShared_6251_ = v_isSharedCheck_6266_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6245_);
                    v_a_6268_ = crate::leanh::lean_ctor_get(v_fst_6247_, 0);
                    crate::leanh::lean_inc(v_a_6268_);
                    crate::leanh::lean_dec_ref_known(v_fst_6247_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6268_) == 0 {
                        v_snd_6269_ = crate::leanh::lean_ctor_get(v_a_6243_, 1);
                        crate::leanh::lean_inc(v_snd_6269_);
                        crate::leanh::lean_dec(v_a_6243_);
                        v_val_6270_ = crate::leanh::lean_ctor_get(v_a_6268_, 0);
                        crate::leanh::lean_inc(v_val_6270_);
                        crate::leanh::lean_dec_ref_known(v_a_6268_, 1);
                        v_a_6222_ = v_val_6270_;
                        v___y_6224_ = v_snd_6269_;
                        state = 0;
                        continue;
                    } else {
                        v_snd_6272_ = crate::leanh::lean_ctor_get(v_a_6243_, 1);
                        crate::leanh::lean_inc(v_snd_6272_);
                        crate::leanh::lean_dec(v_a_6243_);
                        v_val_6273_ = crate::leanh::lean_ctor_get(v_a_6268_, 0);
                        crate::leanh::lean_inc(v_val_6273_);
                        crate::leanh::lean_dec_ref_known(v_a_6268_, 1);
                        v_val_6236_ = v_val_6273_;
                        v_snd_6237_ = v_snd_6272_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                v_a_6252_ = crate::leanh::lean_ctor_get(v_fst_6247_, 0);
                v_isSharedCheck_6265_ = (!crate::leanh::lean_is_exclusive(v_fst_6247_)) as u8;
                if v_isSharedCheck_6265_ == 0 {
                    v___x_6254_ = v_fst_6247_;
                    v_isShared_6255_ = v_isSharedCheck_6265_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6252_);
                    crate::leanh::lean_dec(v_fst_6247_);
                    v___x_6254_ = crate::leanh::lean_box(0);
                    v_isShared_6255_ = v_isSharedCheck_6265_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6255_ == 0 {
                    v___x_6257_ = v___x_6254_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6264_, 0, v_a_6252_);
                    v___x_6257_ = v_reuseFailAlloc_6264_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6251_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6250_, 0, v___x_6257_);
                    v___x_6259_ = v___x_6250_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6263_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6263_, 0, v___x_6257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6263_, 1, v_snd_6248_);
                    v___x_6259_ = v_reuseFailAlloc_6263_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6245_, 0, v___x_6259_);
                    v___x_6261_ = v___x_6245_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6262_, 0, v___x_6259_);
                    v___x_6261_ = v_reuseFailAlloc_6262_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6261_;
            }
            9 => {
                if v_isShared_6278_ == 0 {
                    v___x_6280_ = v___x_6277_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6281_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6281_, 0, v_a_6275_);
                    v___x_6280_ = v_reuseFailAlloc_6281_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6280_;
            }
            11 => {
                v_a_6296_ = crate::leanh::lean_ctor_get(v_fst_6291_, 0);
                v_isSharedCheck_6307_ = (!crate::leanh::lean_is_exclusive(v_fst_6291_)) as u8;
                if v_isSharedCheck_6307_ == 0 {
                    v___x_6298_ = v_fst_6291_;
                    v_isShared_6299_ = v_isSharedCheck_6307_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6296_);
                    crate::leanh::lean_dec(v_fst_6291_);
                    v___x_6298_ = crate::leanh::lean_box(0);
                    v_isShared_6299_ = v_isSharedCheck_6307_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_6299_ == 0 {
                    v___x_6301_ = v___x_6298_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6306_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6306_, 0, v_a_6296_);
                    v___x_6301_ = v_reuseFailAlloc_6306_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_6295_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6294_, 0, v___x_6301_);
                    v___x_6303_ = v___x_6294_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6305_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6305_, 0, v___x_6301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6305_, 1, v_snd_6292_);
                    v___x_6303_ = v_reuseFailAlloc_6305_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_6304_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg___lam__0(v___x_6303_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
                v___y_6242_ = v___x_6304_;
                state = 2;
                continue;
            }
            15 => {
                v_a_6318_ = crate::leanh::lean_ctor_get(v_fst_6313_, 0);
                v_isSharedCheck_6329_ = (!crate::leanh::lean_is_exclusive(v_fst_6313_)) as u8;
                if v_isSharedCheck_6329_ == 0 {
                    v___x_6320_ = v_fst_6313_;
                    v_isShared_6321_ = v_isSharedCheck_6329_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6318_);
                    crate::leanh::lean_dec(v_fst_6313_);
                    v___x_6320_ = crate::leanh::lean_box(0);
                    v_isShared_6321_ = v_isSharedCheck_6329_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_6321_ == 0 {
                    v___x_6323_ = v___x_6320_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6328_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6328_, 0, v_a_6318_);
                    v___x_6323_ = v_reuseFailAlloc_6328_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_6317_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6316_, 0, v___x_6323_);
                    v___x_6325_ = v___x_6316_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6327_, 0, v___x_6323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6327_, 1, v_snd_6314_);
                    v___x_6325_ = v_reuseFailAlloc_6327_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_6326_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg___lam__0(v___x_6325_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
                v___y_6242_ = v___x_6326_;
                state = 2;
                continue;
            }
            19 => {
                v___x_6336_ = (crate::leanh::lean_unbox(v_a_6332_) as u8);
                crate::leanh::lean_dec(v_a_6332_);
                if v___x_6336_ == 0 {
                    crate::leanh::lean_del_object(v___x_6334_);
                    v_snd_6337_ = crate::leanh::lean_ctor_get(v_a_6312_, 1);
                    crate::leanh::lean_inc(v_snd_6337_);
                    crate::leanh::lean_dec(v_a_6312_);
                    v___x_6338_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__8___redArg(v___x_6288_, v_snd_6337_);
                    crate::leanh::lean_dec(v___x_6288_);
                    if crate::leanh::lean_obj_tag(v___x_6338_) == 0 {
                        v_a_6339_ = crate::leanh::lean_ctor_get(v___x_6338_, 0);
                        crate::leanh::lean_inc(v_a_6339_);
                        crate::leanh::lean_dec_ref_known(v___x_6338_, 1);
                        v_fst_6340_ = crate::leanh::lean_ctor_get(v_a_6339_, 0);
                        crate::leanh::lean_inc(v_fst_6340_);
                        if crate::leanh::lean_obj_tag(v_fst_6340_) == 0 {
                            crate::leanh::lean_dec(v___x_6287_);
                            v_snd_6341_ = crate::leanh::lean_ctor_get(v_a_6339_, 1);
                            v_isSharedCheck_6357_ =
                                (!crate::leanh::lean_is_exclusive(v_a_6339_)) as u8;
                            if v_isSharedCheck_6357_ == 0 {
                                v_unused_6358_ = crate::leanh::lean_ctor_get(v_a_6339_, 0);
                                crate::leanh::lean_dec(v_unused_6358_);
                                v___x_6343_ = v_a_6339_;
                                v_isShared_6344_ = v_isSharedCheck_6357_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_6341_);
                                crate::leanh::lean_dec(v_a_6339_);
                                v___x_6343_ = crate::leanh::lean_box(0);
                                v_isShared_6344_ = v_isSharedCheck_6357_;
                                state = 20;
                                continue;
                            }
                        } else {
                            v_snd_6359_ = crate::leanh::lean_ctor_get(v_a_6339_, 1);
                            v_isSharedCheck_6376_ =
                                (!crate::leanh::lean_is_exclusive(v_a_6339_)) as u8;
                            if v_isSharedCheck_6376_ == 0 {
                                v_unused_6377_ = crate::leanh::lean_ctor_get(v_a_6339_, 0);
                                crate::leanh::lean_dec(v_unused_6377_);
                                v___x_6361_ = v_a_6339_;
                                v_isShared_6362_ = v_isSharedCheck_6376_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_6359_);
                                crate::leanh::lean_dec(v_a_6339_);
                                v___x_6361_ = crate::leanh::lean_box(0);
                                v_isShared_6362_ = v_isSharedCheck_6376_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6287_);
                        v_a_6378_ = crate::leanh::lean_ctor_get(v___x_6338_, 0);
                        v_isSharedCheck_6385_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6338_)) as u8;
                        if v_isSharedCheck_6385_ == 0 {
                            v___x_6380_ = v___x_6338_;
                            v_isShared_6381_ = v_isSharedCheck_6385_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6378_);
                            crate::leanh::lean_dec(v___x_6338_);
                            v___x_6380_ = crate::leanh::lean_box(0);
                            v_isShared_6381_ = v_isSharedCheck_6385_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6288_);
                    v_snd_6386_ = crate::leanh::lean_ctor_get(v_a_6312_, 1);
                    v_isSharedCheck_6398_ = (!crate::leanh::lean_is_exclusive(v_a_6312_)) as u8;
                    if v_isSharedCheck_6398_ == 0 {
                        v_unused_6399_ = crate::leanh::lean_ctor_get(v_a_6312_, 0);
                        crate::leanh::lean_dec(v_unused_6399_);
                        v___x_6388_ = v_a_6312_;
                        v_isShared_6389_ = v_isSharedCheck_6398_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6386_);
                        crate::leanh::lean_dec(v_a_6312_);
                        v___x_6388_ = crate::leanh::lean_box(0);
                        v_isShared_6389_ = v_isSharedCheck_6398_;
                        state = 30;
                        continue;
                    }
                }
            }
            20 => {
                v_a_6345_ = crate::leanh::lean_ctor_get(v_fst_6340_, 0);
                v_isSharedCheck_6356_ = (!crate::leanh::lean_is_exclusive(v_fst_6340_)) as u8;
                if v_isSharedCheck_6356_ == 0 {
                    v___x_6347_ = v_fst_6340_;
                    v_isShared_6348_ = v_isSharedCheck_6356_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6345_);
                    crate::leanh::lean_dec(v_fst_6340_);
                    v___x_6347_ = crate::leanh::lean_box(0);
                    v_isShared_6348_ = v_isSharedCheck_6356_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_6348_ == 0 {
                    v___x_6350_ = v___x_6347_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6355_, 0, v_a_6345_);
                    v___x_6350_ = v_reuseFailAlloc_6355_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_6344_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6343_, 0, v___x_6350_);
                    v___x_6352_ = v___x_6343_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6354_, 0, v___x_6350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6354_, 1, v_snd_6341_);
                    v___x_6352_ = v_reuseFailAlloc_6354_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_6353_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg___lam__0(v___x_6352_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
                v___y_6242_ = v___x_6353_;
                state = 2;
                continue;
            }
            24 => {
                v_isSharedCheck_6374_ = (!crate::leanh::lean_is_exclusive(v_fst_6340_)) as u8;
                if v_isSharedCheck_6374_ == 0 {
                    v_unused_6375_ = crate::leanh::lean_ctor_get(v_fst_6340_, 0);
                    crate::leanh::lean_dec(v_unused_6375_);
                    v___x_6364_ = v_fst_6340_;
                    v_isShared_6365_ = v_isSharedCheck_6374_;
                    state = 25;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_6340_);
                    v___x_6364_ = crate::leanh::lean_box(0);
                    v_isShared_6365_ = v_isSharedCheck_6374_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_6366_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6366_, 0, v___x_6287_);
                if v_isShared_6365_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6364_, 0, v___x_6366_);
                    v___x_6368_ = v___x_6364_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6373_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6373_, 0, v___x_6366_);
                    v___x_6368_ = v_reuseFailAlloc_6373_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_6362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6361_, 0, v___x_6368_);
                    v___x_6370_ = v___x_6361_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6372_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 0, v___x_6368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 1, v_snd_6359_);
                    v___x_6370_ = v_reuseFailAlloc_6372_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_6371_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg___lam__0(v___x_6370_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
                v___y_6242_ = v___x_6371_;
                state = 2;
                continue;
            }
            28 => {
                if v_isShared_6381_ == 0 {
                    v___x_6383_ = v___x_6380_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6384_, 0, v_a_6378_);
                    v___x_6383_ = v_reuseFailAlloc_6384_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6383_;
            }
            30 => {
                v___x_6390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6390_, 0, v___x_6287_);
                if v_isShared_6335_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6334_, 0, v___x_6390_);
                    v___x_6392_ = v___x_6334_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_6397_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6397_, 0, v___x_6390_);
                    v___x_6392_ = v_reuseFailAlloc_6397_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                if v_isShared_6389_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6388_, 0, v___x_6392_);
                    v___x_6394_ = v___x_6388_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6396_, 0, v___x_6392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6396_, 1, v_snd_6386_);
                    v___x_6394_ = v_reuseFailAlloc_6396_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_6395_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg___lam__0(v___x_6394_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_, v___y_6233_);
                v___y_6242_ = v___x_6395_;
                state = 2;
                continue;
            }
            33 => {
                if v_isShared_6404_ == 0 {
                    v___x_6406_ = v___x_6403_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6407_, 0, v_a_6401_);
                    v___x_6406_ = v_reuseFailAlloc_6407_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6406_;
            }
            35 => {
                if v_isShared_6412_ == 0 {
                    v___x_6414_ = v___x_6411_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_6415_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6415_, 0, v_a_6409_);
                    v___x_6414_ = v_reuseFailAlloc_6415_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_6414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg___boxed(
    mut v_a_6417_: *mut crate::leanh::LeanObject,
    mut v___y_6418_: *mut crate::leanh::LeanObject,
    mut v___y_6419_: *mut crate::leanh::LeanObject,
    mut v___y_6420_: *mut crate::leanh::LeanObject,
    mut v___y_6421_: *mut crate::leanh::LeanObject,
    mut v___y_6422_: *mut crate::leanh::LeanObject,
    mut v___y_6423_: *mut crate::leanh::LeanObject,
    mut v___y_6424_: *mut crate::leanh::LeanObject,
    mut v___y_6425_: *mut crate::leanh::LeanObject,
    mut v___y_6426_: *mut crate::leanh::LeanObject,
    mut v___y_6427_: *mut crate::leanh::LeanObject,
    mut v___y_6428_: *mut crate::leanh::LeanObject,
    mut v___y_6429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6430_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg(v_a_6417_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_, v___y_6425_, v___y_6426_, v___y_6427_, v___y_6428_);
    crate::leanh::lean_dec(v___y_6428_);
    crate::leanh::lean_dec_ref(v___y_6427_);
    crate::leanh::lean_dec(v___y_6426_);
    crate::leanh::lean_dec_ref(v___y_6425_);
    crate::leanh::lean_dec(v___y_6424_);
    crate::leanh::lean_dec_ref(v___y_6423_);
    crate::leanh::lean_dec(v___y_6422_);
    crate::leanh::lean_dec_ref(v___y_6421_);
    crate::leanh::lean_dec(v___y_6420_);
    crate::leanh::lean_dec_ref(v___y_6418_);
    return v_res_6430_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3(
    mut v_a_6431_: *mut crate::leanh::LeanObject,
    mut v_a_6432_: *mut crate::leanh::LeanObject,
    mut v___y_6433_: *mut crate::leanh::LeanObject,
    mut v___y_6434_: *mut crate::leanh::LeanObject,
    mut v___y_6435_: *mut crate::leanh::LeanObject,
    mut v___y_6436_: *mut crate::leanh::LeanObject,
    mut v___y_6437_: *mut crate::leanh::LeanObject,
    mut v___y_6438_: *mut crate::leanh::LeanObject,
    mut v___y_6439_: *mut crate::leanh::LeanObject,
    mut v___y_6440_: *mut crate::leanh::LeanObject,
    mut v___y_6441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_added_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6451_: u8 = 0;
    let mut v_fst_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6456_: u8 = 0;
    let mut v_a_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6460_: u8 = 0;
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6470_: u8 = 0;
    let mut v_isSharedCheck_6471_: u8 = 0;
    let mut v_unused_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6476_: u8 = 0;
    let mut v___x_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6484_: u8 = 0;
    let mut v_unused_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6486_: u8 = 0;
    let mut v_a_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6490_: u8 = 0;
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_added_6443_ = crate::leanh::lean_ctor_get(v_a_6432_, 1);
                v___x_6444_ = lean_array_get_size(v_added_6443_);
                v___x_6445_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6446_ = lean_nat_sub(v___x_6444_, v___x_6445_);
                v___x_6447_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg(v___x_6446_, v_a_6431_, v_a_6432_, v___y_6433_, v___y_6434_, v___y_6435_, v___y_6436_, v___y_6437_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_);
                if crate::leanh::lean_obj_tag(v___x_6447_) == 0 {
                    v_a_6448_ = crate::leanh::lean_ctor_get(v___x_6447_, 0);
                    v_isSharedCheck_6486_ = (!crate::leanh::lean_is_exclusive(v___x_6447_)) as u8;
                    if v_isSharedCheck_6486_ == 0 {
                        v___x_6450_ = v___x_6447_;
                        v_isShared_6451_ = v_isSharedCheck_6486_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6448_);
                        crate::leanh::lean_dec(v___x_6447_);
                        v___x_6450_ = crate::leanh::lean_box(0);
                        v_isShared_6451_ = v_isSharedCheck_6486_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6487_ = crate::leanh::lean_ctor_get(v___x_6447_, 0);
                    v_isSharedCheck_6494_ = (!crate::leanh::lean_is_exclusive(v___x_6447_)) as u8;
                    if v_isSharedCheck_6494_ == 0 {
                        v___x_6489_ = v___x_6447_;
                        v_isShared_6490_ = v_isSharedCheck_6494_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6487_);
                        crate::leanh::lean_dec(v___x_6447_);
                        v___x_6489_ = crate::leanh::lean_box(0);
                        v_isShared_6490_ = v_isSharedCheck_6494_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6452_ = crate::leanh::lean_ctor_get(v_a_6448_, 0);
                crate::leanh::lean_inc(v_fst_6452_);
                if crate::leanh::lean_obj_tag(v_fst_6452_) == 0 {
                    v_snd_6453_ = crate::leanh::lean_ctor_get(v_a_6448_, 1);
                    v_isSharedCheck_6471_ = (!crate::leanh::lean_is_exclusive(v_a_6448_)) as u8;
                    if v_isSharedCheck_6471_ == 0 {
                        v_unused_6472_ = crate::leanh::lean_ctor_get(v_a_6448_, 0);
                        crate::leanh::lean_dec(v_unused_6472_);
                        v___x_6455_ = v_a_6448_;
                        v_isShared_6456_ = v_isSharedCheck_6471_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6453_);
                        crate::leanh::lean_dec(v_a_6448_);
                        v___x_6455_ = crate::leanh::lean_box(0);
                        v_isShared_6456_ = v_isSharedCheck_6471_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_fst_6452_, 1);
                    v_snd_6473_ = crate::leanh::lean_ctor_get(v_a_6448_, 1);
                    v_isSharedCheck_6484_ = (!crate::leanh::lean_is_exclusive(v_a_6448_)) as u8;
                    if v_isSharedCheck_6484_ == 0 {
                        v_unused_6485_ = crate::leanh::lean_ctor_get(v_a_6448_, 0);
                        crate::leanh::lean_dec(v_unused_6485_);
                        v___x_6475_ = v_a_6448_;
                        v_isShared_6476_ = v_isSharedCheck_6484_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6473_);
                        crate::leanh::lean_dec(v_a_6448_);
                        v___x_6475_ = crate::leanh::lean_box(0);
                        v_isShared_6476_ = v_isSharedCheck_6484_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_a_6457_ = crate::leanh::lean_ctor_get(v_fst_6452_, 0);
                v_isSharedCheck_6470_ = (!crate::leanh::lean_is_exclusive(v_fst_6452_)) as u8;
                if v_isSharedCheck_6470_ == 0 {
                    v___x_6459_ = v_fst_6452_;
                    v_isShared_6460_ = v_isSharedCheck_6470_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6457_);
                    crate::leanh::lean_dec(v_fst_6452_);
                    v___x_6459_ = crate::leanh::lean_box(0);
                    v_isShared_6460_ = v_isSharedCheck_6470_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6460_ == 0 {
                    v___x_6462_ = v___x_6459_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6469_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6469_, 0, v_a_6457_);
                    v___x_6462_ = v_reuseFailAlloc_6469_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6456_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6455_, 0, v___x_6462_);
                    v___x_6464_ = v___x_6455_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6468_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6468_, 0, v___x_6462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6468_, 1, v_snd_6453_);
                    v___x_6464_ = v_reuseFailAlloc_6468_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_6451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6450_, 0, v___x_6464_);
                    v___x_6466_ = v___x_6450_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6467_, 0, v___x_6464_);
                    v___x_6466_ = v_reuseFailAlloc_6467_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6466_;
            }
            7 => {
                v___x_6477_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
                if v_isShared_6476_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6475_, 0, v___x_6477_);
                    v___x_6479_ = v___x_6475_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6483_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6483_, 0, v___x_6477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6483_, 1, v_snd_6473_);
                    v___x_6479_ = v_reuseFailAlloc_6483_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_6451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6450_, 0, v___x_6479_);
                    v___x_6481_ = v___x_6450_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6482_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6482_, 0, v___x_6479_);
                    v___x_6481_ = v_reuseFailAlloc_6482_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6481_;
            }
            10 => {
                if v_isShared_6490_ == 0 {
                    v___x_6492_ = v___x_6489_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6493_, 0, v_a_6487_);
                    v___x_6492_ = v_reuseFailAlloc_6493_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3___boxed(
    mut v_a_6495_: *mut crate::leanh::LeanObject,
    mut v_a_6496_: *mut crate::leanh::LeanObject,
    mut v___y_6497_: *mut crate::leanh::LeanObject,
    mut v___y_6498_: *mut crate::leanh::LeanObject,
    mut v___y_6499_: *mut crate::leanh::LeanObject,
    mut v___y_6500_: *mut crate::leanh::LeanObject,
    mut v___y_6501_: *mut crate::leanh::LeanObject,
    mut v___y_6502_: *mut crate::leanh::LeanObject,
    mut v___y_6503_: *mut crate::leanh::LeanObject,
    mut v___y_6504_: *mut crate::leanh::LeanObject,
    mut v___y_6505_: *mut crate::leanh::LeanObject,
    mut v___y_6506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6507_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3(v_a_6495_, v_a_6496_, v___y_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_);
    crate::leanh::lean_dec(v___y_6505_);
    crate::leanh::lean_dec_ref(v___y_6504_);
    crate::leanh::lean_dec(v___y_6503_);
    crate::leanh::lean_dec_ref(v___y_6502_);
    crate::leanh::lean_dec(v___y_6501_);
    crate::leanh::lean_dec_ref(v___y_6500_);
    crate::leanh::lean_dec(v___y_6499_);
    crate::leanh::lean_dec_ref(v___y_6498_);
    crate::leanh::lean_dec(v___y_6497_);
    crate::leanh::lean_dec_ref(v_a_6495_);
    return v_res_6507_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1(
    mut v_a_6508_: *mut crate::leanh::LeanObject,
    mut v_a_6509_: *mut crate::leanh::LeanObject,
    mut v___y_6510_: *mut crate::leanh::LeanObject,
    mut v___y_6511_: *mut crate::leanh::LeanObject,
    mut v___y_6512_: *mut crate::leanh::LeanObject,
    mut v___y_6513_: *mut crate::leanh::LeanObject,
    mut v___y_6514_: *mut crate::leanh::LeanObject,
    mut v___y_6515_: *mut crate::leanh::LeanObject,
    mut v___y_6516_: *mut crate::leanh::LeanObject,
    mut v___y_6517_: *mut crate::leanh::LeanObject,
    mut v___y_6518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6525_: u8 = 0;
    let mut v_snd_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6529_: u8 = 0;
    let mut v_found_6530_: u8 = 0;
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6539_: u8 = 0;
    let mut v_unused_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6541_: u8 = 0;
    let mut v_unused_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6520_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2(v_a_6508_, v_a_6509_, v___y_6510_, v___y_6511_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
                if crate::leanh::lean_obj_tag(v___x_6520_) == 0 {
                    v_a_6521_ = crate::leanh::lean_ctor_get(v___x_6520_, 0);
                    crate::leanh::lean_inc(v_a_6521_);
                    v_fst_6522_ = crate::leanh::lean_ctor_get(v_a_6521_, 0);
                    if crate::leanh::lean_obj_tag(v_fst_6522_) == 0 {
                        crate::leanh::lean_dec(v_a_6521_);
                        return v___x_6520_;
                    } else {
                        v_isSharedCheck_6541_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6520_)) as u8;
                        if v_isSharedCheck_6541_ == 0 {
                            v_unused_6542_ = crate::leanh::lean_ctor_get(v___x_6520_, 0);
                            crate::leanh::lean_dec(v_unused_6542_);
                            v___x_6524_ = v___x_6520_;
                            v_isShared_6525_ = v_isSharedCheck_6541_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6520_);
                            v___x_6524_ = crate::leanh::lean_box(0);
                            v_isShared_6525_ = v_isSharedCheck_6541_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___x_6520_;
                }
            }
            1 => {
                v_snd_6526_ = crate::leanh::lean_ctor_get(v_a_6521_, 1);
                v_isSharedCheck_6539_ = (!crate::leanh::lean_is_exclusive(v_a_6521_)) as u8;
                if v_isSharedCheck_6539_ == 0 {
                    v_unused_6540_ = crate::leanh::lean_ctor_get(v_a_6521_, 0);
                    crate::leanh::lean_dec(v_unused_6540_);
                    v___x_6528_ = v_a_6521_;
                    v_isShared_6529_ = v_isSharedCheck_6539_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6526_);
                    crate::leanh::lean_dec(v_a_6521_);
                    v___x_6528_ = crate::leanh::lean_box(0);
                    v_isShared_6529_ = v_isSharedCheck_6539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_found_6530_ = crate::leanh::lean_ctor_get_uint8(
                    v_snd_6526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                if v_found_6530_ == 0 {
                    v___x_6531_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
                    if v_isShared_6529_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6528_, 0, v___x_6531_);
                        v___x_6533_ = v___x_6528_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6537_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6537_, 0, v___x_6531_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6537_, 1, v_snd_6526_);
                        v___x_6533_ = v_reuseFailAlloc_6537_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6528_);
                    crate::leanh::lean_del_object(v___x_6524_);
                    v___x_6538_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3(v_a_6508_, v_snd_6526_, v___y_6510_, v___y_6511_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_);
                    return v___x_6538_;
                }
            }
            3 => {
                if v_isShared_6525_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6524_, 0, v___x_6533_);
                    v___x_6535_ = v___x_6524_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6536_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6536_, 0, v___x_6533_);
                    v___x_6535_ = v_reuseFailAlloc_6536_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1___boxed(
    mut v_a_6543_: *mut crate::leanh::LeanObject,
    mut v_a_6544_: *mut crate::leanh::LeanObject,
    mut v___y_6545_: *mut crate::leanh::LeanObject,
    mut v___y_6546_: *mut crate::leanh::LeanObject,
    mut v___y_6547_: *mut crate::leanh::LeanObject,
    mut v___y_6548_: *mut crate::leanh::LeanObject,
    mut v___y_6549_: *mut crate::leanh::LeanObject,
    mut v___y_6550_: *mut crate::leanh::LeanObject,
    mut v___y_6551_: *mut crate::leanh::LeanObject,
    mut v___y_6552_: *mut crate::leanh::LeanObject,
    mut v___y_6553_: *mut crate::leanh::LeanObject,
    mut v___y_6554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6555_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1(v_a_6543_, v_a_6544_, v___y_6545_, v___y_6546_, v___y_6547_, v___y_6548_, v___y_6549_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_);
    crate::leanh::lean_dec(v___y_6553_);
    crate::leanh::lean_dec_ref(v___y_6552_);
    crate::leanh::lean_dec(v___y_6551_);
    crate::leanh::lean_dec_ref(v___y_6550_);
    crate::leanh::lean_dec(v___y_6549_);
    crate::leanh::lean_dec_ref(v___y_6548_);
    crate::leanh::lean_dec(v___y_6547_);
    crate::leanh::lean_dec_ref(v___y_6546_);
    crate::leanh::lean_dec(v___y_6545_);
    crate::leanh::lean_dec_ref(v_a_6543_);
    return v_res_6555_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1(
    mut v_initialMask_6558_: *mut crate::leanh::LeanObject,
    mut v_test_6559_: *mut crate::leanh::LeanObject,
    mut v_maxCalls_6560_: *mut crate::leanh::LeanObject,
    mut v___y_6561_: *mut crate::leanh::LeanObject,
    mut v___y_6562_: *mut crate::leanh::LeanObject,
    mut v___y_6563_: *mut crate::leanh::LeanObject,
    mut v___y_6564_: *mut crate::leanh::LeanObject,
    mut v___y_6565_: *mut crate::leanh::LeanObject,
    mut v___y_6566_: *mut crate::leanh::LeanObject,
    mut v___y_6567_: *mut crate::leanh::LeanObject,
    mut v___y_6568_: *mut crate::leanh::LeanObject,
    mut v___y_6569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6575_: u8 = 0;
    let mut v___x_6576_: u8 = 0;
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: u8 = 0;
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6586_: u8 = 0;
    let mut v_snd_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_6591_: u8 = 0;
    let mut v___y_6593_: u8 = 0;
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: u8 = 0;
    let mut v___x_6599_: u8 = 0;
    let mut v___x_6600_: u8 = 0;
    let mut v_isSharedCheck_6601_: u8 = 0;
    let mut v_a_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6605_: u8 = 0;
    let mut v___x_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6609_: u8 = 0;
    let mut v___x_6610_: u8 = 0;
    let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6616_: u8 = 0;
    let mut v_a_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6620_: u8 = 0;
    let mut v___x_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_test_6559_);
                crate::leanh::lean_inc(v___y_6569_);
                crate::leanh::lean_inc_ref(v___y_6568_);
                crate::leanh::lean_inc(v___y_6567_);
                crate::leanh::lean_inc_ref(v___y_6566_);
                crate::leanh::lean_inc(v___y_6565_);
                crate::leanh::lean_inc_ref(v___y_6564_);
                crate::leanh::lean_inc(v___y_6563_);
                crate::leanh::lean_inc_ref(v___y_6562_);
                crate::leanh::lean_inc(v___y_6561_);
                crate::leanh::lean_inc_ref(v_initialMask_6558_);
                v___x_6571_ = crate::leanh::lean_apply_11(
                    v_test_6559_,
                    v_initialMask_6558_,
                    v___y_6561_,
                    v___y_6562_,
                    v___y_6563_,
                    v___y_6564_,
                    v___y_6565_,
                    v___y_6566_,
                    v___y_6567_,
                    v___y_6568_,
                    v___y_6569_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6571_) == 0 {
                    v_a_6572_ = crate::leanh::lean_ctor_get(v___x_6571_, 0);
                    v_isSharedCheck_6616_ = (!crate::leanh::lean_is_exclusive(v___x_6571_)) as u8;
                    if v_isSharedCheck_6616_ == 0 {
                        v___x_6574_ = v___x_6571_;
                        v_isShared_6575_ = v_isSharedCheck_6616_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6572_);
                        crate::leanh::lean_dec(v___x_6571_);
                        v___x_6574_ = crate::leanh::lean_box(0);
                        v_isShared_6575_ = v_isSharedCheck_6616_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_maxCalls_6560_);
                    crate::leanh::lean_dec_ref(v_test_6559_);
                    crate::leanh::lean_dec_ref(v_initialMask_6558_);
                    v_a_6617_ = crate::leanh::lean_ctor_get(v___x_6571_, 0);
                    v_isSharedCheck_6624_ = (!crate::leanh::lean_is_exclusive(v___x_6571_)) as u8;
                    if v_isSharedCheck_6624_ == 0 {
                        v___x_6619_ = v___x_6571_;
                        v_isShared_6620_ = v_isSharedCheck_6624_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6617_);
                        crate::leanh::lean_dec(v___x_6571_);
                        v___x_6619_ = crate::leanh::lean_box(0);
                        v_isShared_6620_ = v_isSharedCheck_6624_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6576_ = (crate::leanh::lean_unbox(v_a_6572_) as u8);
                if v___x_6576_ == 0 {
                    crate::leanh::lean_del_object(v___x_6574_);
                    crate::leanh::lean_inc_ref(v_initialMask_6558_);
                    v___x_6577_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6577_, 0, v_initialMask_6558_);
                    crate::leanh::lean_ctor_set(v___x_6577_, 1, v_test_6559_);
                    crate::leanh::lean_ctor_set(v___x_6577_, 2, v_maxCalls_6560_);
                    v___x_6578_ = l_Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1___closed__0;
                    v___x_6579_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6580_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6580_, 0, v_initialMask_6558_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 1, v___x_6578_);
                    crate::leanh::lean_ctor_set(v___x_6580_, 2, v___x_6579_);
                    v___x_6581_ = (crate::leanh::lean_unbox(v_a_6572_) as u8);
                    crate::leanh::lean_dec(v_a_6572_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6580_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v___x_6581_,
                    );
                    v___x_6582_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1(v___x_6577_, v___x_6580_, v___y_6561_, v___y_6562_, v___y_6563_, v___y_6564_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_, v___y_6569_);
                    crate::leanh::lean_dec_ref_known(v___x_6577_, 3);
                    if crate::leanh::lean_obj_tag(v___x_6582_) == 0 {
                        v_a_6583_ = crate::leanh::lean_ctor_get(v___x_6582_, 0);
                        v_isSharedCheck_6601_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6582_)) as u8;
                        if v_isSharedCheck_6601_ == 0 {
                            v___x_6585_ = v___x_6582_;
                            v_isShared_6586_ = v_isSharedCheck_6601_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6583_);
                            crate::leanh::lean_dec(v___x_6582_);
                            v___x_6585_ = crate::leanh::lean_box(0);
                            v_isShared_6586_ = v_isSharedCheck_6601_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_6602_ = crate::leanh::lean_ctor_get(v___x_6582_, 0);
                        v_isSharedCheck_6609_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6582_)) as u8;
                        if v_isSharedCheck_6609_ == 0 {
                            v___x_6604_ = v___x_6582_;
                            v_isShared_6605_ = v_isSharedCheck_6609_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6602_);
                            crate::leanh::lean_dec(v___x_6582_);
                            v___x_6604_ = crate::leanh::lean_box(0);
                            v_isShared_6605_ = v_isSharedCheck_6609_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6572_);
                    crate::leanh::lean_dec(v_maxCalls_6560_);
                    crate::leanh::lean_dec_ref(v_test_6559_);
                    v___x_6610_ = 2;
                    v___x_6611_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6612_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6612_, 0, v_initialMask_6558_);
                    crate::leanh::lean_ctor_set(v___x_6612_, 1, v___x_6611_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6612_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_6610_,
                    );
                    if v_isShared_6575_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6574_, 0, v___x_6612_);
                        v___x_6614_ = v___x_6574_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6615_, 0, v___x_6612_);
                        v___x_6614_ = v_reuseFailAlloc_6615_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_6587_ = crate::leanh::lean_ctor_get(v_a_6583_, 1);
                crate::leanh::lean_inc(v_snd_6587_);
                v_fst_6588_ = crate::leanh::lean_ctor_get(v_a_6583_, 0);
                crate::leanh::lean_inc(v_fst_6588_);
                crate::leanh::lean_dec(v_a_6583_);
                v_cur_6589_ = crate::leanh::lean_ctor_get(v_snd_6587_, 0);
                crate::leanh::lean_inc_ref(v_cur_6589_);
                v_numCalls_6590_ = crate::leanh::lean_ctor_get(v_snd_6587_, 2);
                crate::leanh::lean_inc(v_numCalls_6590_);
                v_found_6591_ = crate::leanh::lean_ctor_get_uint8(
                    v_snd_6587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec(v_snd_6587_);
                if v_found_6591_ == 0 {
                    crate::leanh::lean_dec(v_fst_6588_);
                    v___x_6598_ = 0;
                    v___y_6593_ = v___x_6598_;
                    state = 3;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v_fst_6588_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_fst_6588_, 1);
                        v___x_6599_ = 1;
                        v___y_6593_ = v___x_6599_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_fst_6588_, 1);
                        v___x_6600_ = 2;
                        v___y_6593_ = v___x_6600_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6594_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_6594_, 0, v_cur_6589_);
                crate::leanh::lean_ctor_set(v___x_6594_, 1, v_numCalls_6590_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6594_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_6593_,
                );
                if v_isShared_6586_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6585_, 0, v___x_6594_);
                    v___x_6596_ = v___x_6585_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6597_, 0, v___x_6594_);
                    v___x_6596_ = v_reuseFailAlloc_6597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6596_;
            }
            5 => {
                if v_isShared_6605_ == 0 {
                    v___x_6607_ = v___x_6604_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6608_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6608_, 0, v_a_6602_);
                    v___x_6607_ = v_reuseFailAlloc_6608_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6607_;
            }
            7 => {
                return v___x_6614_;
            }
            8 => {
                if v_isShared_6620_ == 0 {
                    v___x_6622_ = v___x_6619_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6623_, 0, v_a_6617_);
                    v___x_6622_ = v_reuseFailAlloc_6623_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1___boxed(
    mut v_initialMask_6625_: *mut crate::leanh::LeanObject,
    mut v_test_6626_: *mut crate::leanh::LeanObject,
    mut v_maxCalls_6627_: *mut crate::leanh::LeanObject,
    mut v___y_6628_: *mut crate::leanh::LeanObject,
    mut v___y_6629_: *mut crate::leanh::LeanObject,
    mut v___y_6630_: *mut crate::leanh::LeanObject,
    mut v___y_6631_: *mut crate::leanh::LeanObject,
    mut v___y_6632_: *mut crate::leanh::LeanObject,
    mut v___y_6633_: *mut crate::leanh::LeanObject,
    mut v___y_6634_: *mut crate::leanh::LeanObject,
    mut v___y_6635_: *mut crate::leanh::LeanObject,
    mut v___y_6636_: *mut crate::leanh::LeanObject,
    mut v___y_6637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6638_ =
        l_Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1(
            v_initialMask_6625_,
            v_test_6626_,
            v_maxCalls_6627_,
            v___y_6628_,
            v___y_6629_,
            v___y_6630_,
            v___y_6631_,
            v___y_6632_,
            v___y_6633_,
            v___y_6634_,
            v___y_6635_,
            v___y_6636_,
        );
    crate::leanh::lean_dec(v___y_6636_);
    crate::leanh::lean_dec_ref(v___y_6635_);
    crate::leanh::lean_dec(v___y_6634_);
    crate::leanh::lean_dec_ref(v___y_6633_);
    crate::leanh::lean_dec(v___y_6632_);
    crate::leanh::lean_dec_ref(v___y_6631_);
    crate::leanh::lean_dec(v___y_6630_);
    crate::leanh::lean_dec_ref(v___y_6629_);
    crate::leanh::lean_dec(v___y_6628_);
    return v_res_6638_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instantiate_x27(
    mut v_goal_6641_: *mut crate::leanh::LeanObject,
    mut v_kna_6642_: *mut crate::leanh::LeanObject,
    mut v_kp_6643_: *mut crate::leanh::LeanObject,
    mut v_a_6644_: *mut crate::leanh::LeanObject,
    mut v_a_6645_: *mut crate::leanh::LeanObject,
    mut v_a_6646_: *mut crate::leanh::LeanObject,
    mut v_a_6647_: *mut crate::leanh::LeanObject,
    mut v_a_6648_: *mut crate::leanh::LeanObject,
    mut v_a_6649_: *mut crate::leanh::LeanObject,
    mut v_a_6650_: *mut crate::leanh::LeanObject,
    mut v_a_6651_: *mut crate::leanh::LeanObject,
    mut v_a_6652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_newSeq_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: u8 = 0;
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seq_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6679_: u8 = 0;
    let mut v_trace_6680_: u8 = 0;
    let mut v___x_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_status_6697_: u8 = 0;
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6703_: u8 = 0;
    let mut v___x_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6707_: u8 = 0;
    let mut v_paramMask_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6715_: u8 = 0;
    let mut v___x_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6719_: u8 = 0;
    let mut v_paramMask_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: u8 = 0;
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6728_: u8 = 0;
    let mut v___x_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6732_: u8 = 0;
    let mut v_a_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6736_: u8 = 0;
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6740_: u8 = 0;
    let mut v_a_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6744_: u8 = 0;
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6748_: u8 = 0;
    let mut v_isSharedCheck_6749_: u8 = 0;
    let mut v_a_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6753_: u8 = 0;
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6757_: u8 = 0;
    let mut v_a_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6761_: u8 = 0;
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6765_: u8 = 0;
    let mut v_a_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6769_: u8 = 0;
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6658_ = l_Lean_Meta_Grind_Action_saveStateIfTracing___redArg(
                    v_a_6645_, v_a_6646_, v_a_6650_, v_a_6652_,
                );
                if crate::leanh::lean_obj_tag(v___x_6658_) == 0 {
                    v_a_6659_ = crate::leanh::lean_ctor_get(v___x_6658_, 0);
                    crate::leanh::lean_inc(v_a_6659_);
                    crate::leanh::lean_dec_ref_known(v___x_6658_, 1);
                    v_mvarId_6660_ = crate::leanh::lean_ctor_get(v_goal_6641_, 1);
                    v___x_6661_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6662_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect___closed__2;
                    crate::leanh::lean_inc_ref(v_goal_6641_);
                    v___f_6663_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Action_instantiate_x27___lam__0___boxed
                            as *mut core::ffi::c_void,
                        12,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_6663_, 0, v_goal_6641_);
                    crate::leanh::lean_closure_set(v___f_6663_, 1, v___x_6662_);
                    crate::leanh::lean_inc(v_mvarId_6660_);
                    v___x_6664_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkInstantiateTactic_spec__3___redArg(v_mvarId_6660_, v___f_6663_, v_a_6644_, v_a_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                    if crate::leanh::lean_obj_tag(v___x_6664_) == 0 {
                        v_a_6665_ = crate::leanh::lean_ctor_get(v___x_6664_, 0);
                        crate::leanh::lean_inc(v_a_6665_);
                        crate::leanh::lean_dec_ref_known(v___x_6664_, 1);
                        v_fst_6666_ = crate::leanh::lean_ctor_get(v_a_6665_, 0);
                        crate::leanh::lean_inc(v_fst_6666_);
                        v_fst_6667_ = crate::leanh::lean_ctor_get(v_fst_6666_, 0);
                        v___x_6668_ = (crate::leanh::lean_unbox(v_fst_6667_) as u8);
                        if v___x_6668_ == 0 {
                            crate::leanh::lean_dec(v_fst_6666_);
                            crate::leanh::lean_dec(v_a_6665_);
                            crate::leanh::lean_dec(v_a_6659_);
                            crate::leanh::lean_dec_ref(v_kp_6643_);
                            crate::leanh::lean_inc(v_a_6652_);
                            crate::leanh::lean_inc_ref(v_a_6651_);
                            crate::leanh::lean_inc(v_a_6650_);
                            crate::leanh::lean_inc_ref(v_a_6649_);
                            crate::leanh::lean_inc(v_a_6648_);
                            crate::leanh::lean_inc_ref(v_a_6647_);
                            crate::leanh::lean_inc(v_a_6646_);
                            crate::leanh::lean_inc_ref(v_a_6645_);
                            crate::leanh::lean_inc(v_a_6644_);
                            v___x_6669_ = crate::leanh::lean_apply_11(
                                v_kna_6642_,
                                v_goal_6641_,
                                v_a_6644_,
                                v_a_6645_,
                                v_a_6646_,
                                v_a_6647_,
                                v_a_6648_,
                                v_a_6649_,
                                v_a_6650_,
                                v_a_6651_,
                                v_a_6652_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_6669_;
                        } else {
                            crate::leanh::lean_dec_ref(v_kna_6642_);
                            v_snd_6670_ = crate::leanh::lean_ctor_get(v_a_6665_, 1);
                            crate::leanh::lean_inc(v_snd_6670_);
                            crate::leanh::lean_dec(v_a_6665_);
                            v_snd_6671_ = crate::leanh::lean_ctor_get(v_fst_6666_, 1);
                            crate::leanh::lean_inc(v_snd_6671_);
                            crate::leanh::lean_dec(v_fst_6666_);
                            crate::leanh::lean_inc(v_a_6652_);
                            crate::leanh::lean_inc_ref(v_a_6651_);
                            crate::leanh::lean_inc(v_a_6650_);
                            crate::leanh::lean_inc_ref(v_a_6649_);
                            crate::leanh::lean_inc(v_a_6648_);
                            crate::leanh::lean_inc_ref(v_a_6647_);
                            crate::leanh::lean_inc(v_a_6646_);
                            crate::leanh::lean_inc_ref(v_a_6645_);
                            crate::leanh::lean_inc(v_a_6644_);
                            v___x_6672_ = crate::leanh::lean_apply_11(
                                v_kp_6643_,
                                v_snd_6670_,
                                v_a_6644_,
                                v_a_6645_,
                                v_a_6646_,
                                v_a_6647_,
                                v_a_6648_,
                                v_a_6649_,
                                v_a_6650_,
                                v_a_6651_,
                                v_a_6652_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_6672_) == 0 {
                                v_a_6673_ = crate::leanh::lean_ctor_get(v___x_6672_, 0);
                                crate::leanh::lean_inc(v_a_6673_);
                                if crate::leanh::lean_obj_tag(v_a_6673_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6672_, 1);
                                    v_seq_6674_ = crate::leanh::lean_ctor_get(v_a_6673_, 0);
                                    crate::leanh::lean_inc(v_seq_6674_);
                                    crate::leanh::lean_dec_ref_known(v_a_6673_, 1);
                                    v___x_6675_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_6645_);
                                    if crate::leanh::lean_obj_tag(v___x_6675_) == 0 {
                                        v_a_6676_ = crate::leanh::lean_ctor_get(v___x_6675_, 0);
                                        v_isSharedCheck_6749_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6675_)) as u8;
                                        if v_isSharedCheck_6749_ == 0 {
                                            v___x_6678_ = v___x_6675_;
                                            v_isShared_6679_ = v_isSharedCheck_6749_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6676_);
                                            crate::leanh::lean_dec(v___x_6675_);
                                            v___x_6678_ = crate::leanh::lean_box(0);
                                            v_isShared_6679_ = v_isSharedCheck_6749_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_seq_6674_);
                                        crate::leanh::lean_dec(v_snd_6671_);
                                        crate::leanh::lean_dec(v_a_6659_);
                                        crate::leanh::lean_dec_ref(v_goal_6641_);
                                        v_a_6750_ = crate::leanh::lean_ctor_get(v___x_6675_, 0);
                                        v_isSharedCheck_6757_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6675_)) as u8;
                                        if v_isSharedCheck_6757_ == 0 {
                                            v___x_6752_ = v___x_6675_;
                                            v_isShared_6753_ = v_isSharedCheck_6757_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6750_);
                                            crate::leanh::lean_dec(v___x_6675_);
                                            v___x_6752_ = crate::leanh::lean_box(0);
                                            v_isShared_6753_ = v_isSharedCheck_6757_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6673_);
                                    crate::leanh::lean_dec(v_snd_6671_);
                                    crate::leanh::lean_dec(v_a_6659_);
                                    crate::leanh::lean_dec_ref(v_goal_6641_);
                                    return v___x_6672_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_6671_);
                                crate::leanh::lean_dec(v_a_6659_);
                                crate::leanh::lean_dec_ref(v_goal_6641_);
                                return v___x_6672_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6659_);
                        crate::leanh::lean_dec_ref(v_kp_6643_);
                        crate::leanh::lean_dec_ref(v_kna_6642_);
                        crate::leanh::lean_dec_ref(v_goal_6641_);
                        v_a_6758_ = crate::leanh::lean_ctor_get(v___x_6664_, 0);
                        v_isSharedCheck_6765_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6664_)) as u8;
                        if v_isSharedCheck_6765_ == 0 {
                            v___x_6760_ = v___x_6664_;
                            v_isShared_6761_ = v_isSharedCheck_6765_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6758_);
                            crate::leanh::lean_dec(v___x_6664_);
                            v___x_6760_ = crate::leanh::lean_box(0);
                            v_isShared_6761_ = v_isSharedCheck_6765_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_kp_6643_);
                    crate::leanh::lean_dec_ref(v_kna_6642_);
                    crate::leanh::lean_dec_ref(v_goal_6641_);
                    v_a_6766_ = crate::leanh::lean_ctor_get(v___x_6658_, 0);
                    v_isSharedCheck_6773_ = (!crate::leanh::lean_is_exclusive(v___x_6658_)) as u8;
                    if v_isSharedCheck_6773_ == 0 {
                        v___x_6768_ = v___x_6658_;
                        v_isShared_6769_ = v_isSharedCheck_6773_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6766_);
                        crate::leanh::lean_dec(v___x_6658_);
                        v___x_6768_ = crate::leanh::lean_box(0);
                        v_isShared_6769_ = v_isSharedCheck_6773_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6656_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6656_, 0, v_newSeq_6655_);
                v___x_6657_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6657_, 0, v___x_6656_);
                return v___x_6657_;
            }
            2 => {
                v_trace_6680_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6676_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                crate::leanh::lean_dec(v_a_6676_);
                if v_trace_6680_ == 0 {
                    crate::leanh::lean_dec(v_seq_6674_);
                    crate::leanh::lean_dec(v_snd_6671_);
                    crate::leanh::lean_dec(v_a_6659_);
                    crate::leanh::lean_dec_ref(v_goal_6641_);
                    v___x_6681_ = l_Lean_Meta_Grind_Action_instantiate_x27___closed__0;
                    if v_isShared_6679_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6678_, 0, v___x_6681_);
                        v___x_6683_ = v___x_6678_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6684_, 0, v___x_6681_);
                        v___x_6683_ = v_reuseFailAlloc_6684_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6678_);
                    crate::leanh::lean_inc(v_mvarId_6660_);
                    v___x_6685_ = l_Lean_mkMVar(v_mvarId_6660_);
                    v___x_6686_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__0___redArg(v___x_6685_, v_a_6650_);
                    v_a_6687_ = crate::leanh::lean_ctor_get(v___x_6686_, 0);
                    crate::leanh::lean_inc(v_a_6687_);
                    crate::leanh::lean_dec_ref(v___x_6686_);
                    v___x_6688_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_getAllTheorems(v_snd_6671_);
                    v_fst_6689_ = crate::leanh::lean_ctor_get(v___x_6688_, 0);
                    crate::leanh::lean_inc(v_fst_6689_);
                    v_snd_6690_ = crate::leanh::lean_ctor_get(v___x_6688_, 1);
                    crate::leanh::lean_inc(v_snd_6690_);
                    crate::leanh::lean_dec_ref(v___x_6688_);
                    v___x_6691_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_collect(v_a_6687_, v_snd_6671_);
                    crate::leanh::lean_dec(v_snd_6671_);
                    v___x_6692_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkMask(v_snd_6690_, v___x_6691_, v_a_6651_, v_a_6652_);
                    crate::leanh::lean_dec_ref(v___x_6691_);
                    if crate::leanh::lean_obj_tag(v___x_6692_) == 0 {
                        v_a_6693_ = crate::leanh::lean_ctor_get(v___x_6692_, 0);
                        crate::leanh::lean_inc(v_a_6693_);
                        crate::leanh::lean_dec_ref_known(v___x_6692_, 1);
                        crate::leanh::lean_inc(v_seq_6674_);
                        crate::leanh::lean_inc_ref(v_goal_6641_);
                        crate::leanh::lean_inc(v_fst_6689_);
                        v___f_6694_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_Action_instantiate_x27___lam__1___boxed
                                as *mut core::ffi::c_void,
                            15,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___f_6694_, 0, v_fst_6689_);
                        crate::leanh::lean_closure_set(v___f_6694_, 1, v_goal_6641_);
                        crate::leanh::lean_closure_set(v___f_6694_, 2, v_seq_6674_);
                        crate::leanh::lean_closure_set(v___f_6694_, 3, v_a_6659_);
                        v___x_6695_ = l_Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1(v_a_6693_, v___f_6694_, v___x_6661_, v_a_6644_, v_a_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                        if crate::leanh::lean_obj_tag(v___x_6695_) == 0 {
                            v_a_6696_ = crate::leanh::lean_ctor_get(v___x_6695_, 0);
                            crate::leanh::lean_inc(v_a_6696_);
                            crate::leanh::lean_dec_ref_known(v___x_6695_, 1);
                            v_status_6697_ = crate::leanh::lean_ctor_get_uint8(
                                v_a_6696_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                            );
                            match v_status_6697_ {
                                0 => {
                                    crate::leanh::lean_dec(v_a_6696_);
                                    crate::leanh::lean_dec(v_fst_6689_);
                                    v___x_6698_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkNewSeq(v_goal_6641_, v___x_6662_, v_seq_6674_, v_trace_6680_, v_a_6644_, v_a_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                                    if crate::leanh::lean_obj_tag(v___x_6698_) == 0 {
                                        v_a_6699_ = crate::leanh::lean_ctor_get(v___x_6698_, 0);
                                        crate::leanh::lean_inc(v_a_6699_);
                                        crate::leanh::lean_dec_ref_known(v___x_6698_, 1);
                                        v_newSeq_6655_ = v_a_6699_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_a_6700_ = crate::leanh::lean_ctor_get(v___x_6698_, 0);
                                        v_isSharedCheck_6707_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6698_)) as u8;
                                        if v_isSharedCheck_6707_ == 0 {
                                            v___x_6702_ = v___x_6698_;
                                            v_isShared_6703_ = v_isSharedCheck_6707_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6700_);
                                            crate::leanh::lean_dec(v___x_6698_);
                                            v___x_6702_ = crate::leanh::lean_box(0);
                                            v_isShared_6703_ = v_isSharedCheck_6707_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                }
                                1 => {
                                    v_paramMask_6708_ = crate::leanh::lean_ctor_get(v_a_6696_, 0);
                                    crate::leanh::lean_inc_ref(v_paramMask_6708_);
                                    crate::leanh::lean_dec(v_a_6696_);
                                    v___x_6709_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms(v_fst_6689_, v_paramMask_6708_);
                                    crate::leanh::lean_dec_ref(v_paramMask_6708_);
                                    crate::leanh::lean_dec(v_fst_6689_);
                                    v___x_6710_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkNewSeq(v_goal_6641_, v___x_6709_, v_seq_6674_, v_trace_6680_, v_a_6644_, v_a_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                                    if crate::leanh::lean_obj_tag(v___x_6710_) == 0 {
                                        v_a_6711_ = crate::leanh::lean_ctor_get(v___x_6710_, 0);
                                        crate::leanh::lean_inc(v_a_6711_);
                                        crate::leanh::lean_dec_ref_known(v___x_6710_, 1);
                                        v_newSeq_6655_ = v_a_6711_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_a_6712_ = crate::leanh::lean_ctor_get(v___x_6710_, 0);
                                        v_isSharedCheck_6719_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6710_)) as u8;
                                        if v_isSharedCheck_6719_ == 0 {
                                            v___x_6714_ = v___x_6710_;
                                            v_isShared_6715_ = v_isSharedCheck_6719_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6712_);
                                            crate::leanh::lean_dec(v___x_6710_);
                                            v___x_6714_ = crate::leanh::lean_box(0);
                                            v_isShared_6715_ = v_isSharedCheck_6719_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                                _ => {
                                    v_paramMask_6720_ = crate::leanh::lean_ctor_get(v_a_6696_, 0);
                                    crate::leanh::lean_inc_ref(v_paramMask_6720_);
                                    crate::leanh::lean_dec(v_a_6696_);
                                    v___x_6721_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_maskToThms(v_fst_6689_, v_paramMask_6720_);
                                    crate::leanh::lean_dec_ref(v_paramMask_6720_);
                                    crate::leanh::lean_dec(v_fst_6689_);
                                    v___x_6722_ = 0;
                                    v___x_6723_ = l___private_Lean_Meta_Tactic_Grind_EMatchAction_0__Lean_Meta_Grind_Action_mkNewSeq(v_goal_6641_, v___x_6721_, v_seq_6674_, v___x_6722_, v_a_6644_, v_a_6645_, v_a_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_, v_a_6651_, v_a_6652_);
                                    if crate::leanh::lean_obj_tag(v___x_6723_) == 0 {
                                        v_a_6724_ = crate::leanh::lean_ctor_get(v___x_6723_, 0);
                                        crate::leanh::lean_inc(v_a_6724_);
                                        crate::leanh::lean_dec_ref_known(v___x_6723_, 1);
                                        v_newSeq_6655_ = v_a_6724_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_a_6725_ = crate::leanh::lean_ctor_get(v___x_6723_, 0);
                                        v_isSharedCheck_6732_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6723_)) as u8;
                                        if v_isSharedCheck_6732_ == 0 {
                                            v___x_6727_ = v___x_6723_;
                                            v_isShared_6728_ = v_isSharedCheck_6732_;
                                            state = 8;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6725_);
                                            crate::leanh::lean_dec(v___x_6723_);
                                            v___x_6727_ = crate::leanh::lean_box(0);
                                            v_isShared_6728_ = v_isSharedCheck_6732_;
                                            state = 8;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_6689_);
                            crate::leanh::lean_dec(v_seq_6674_);
                            crate::leanh::lean_dec_ref(v_goal_6641_);
                            v_a_6733_ = crate::leanh::lean_ctor_get(v___x_6695_, 0);
                            v_isSharedCheck_6740_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6695_)) as u8;
                            if v_isSharedCheck_6740_ == 0 {
                                v___x_6735_ = v___x_6695_;
                                v_isShared_6736_ = v_isSharedCheck_6740_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6733_);
                                crate::leanh::lean_dec(v___x_6695_);
                                v___x_6735_ = crate::leanh::lean_box(0);
                                v_isShared_6736_ = v_isSharedCheck_6740_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_6689_);
                        crate::leanh::lean_dec(v_seq_6674_);
                        crate::leanh::lean_dec(v_a_6659_);
                        crate::leanh::lean_dec_ref(v_goal_6641_);
                        v_a_6741_ = crate::leanh::lean_ctor_get(v___x_6692_, 0);
                        v_isSharedCheck_6748_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6692_)) as u8;
                        if v_isSharedCheck_6748_ == 0 {
                            v___x_6743_ = v___x_6692_;
                            v_isShared_6744_ = v_isSharedCheck_6748_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6741_);
                            crate::leanh::lean_dec(v___x_6692_);
                            v___x_6743_ = crate::leanh::lean_box(0);
                            v_isShared_6744_ = v_isSharedCheck_6748_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_6683_;
            }
            4 => {
                if v_isShared_6703_ == 0 {
                    v___x_6705_ = v___x_6702_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6706_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6706_, 0, v_a_6700_);
                    v___x_6705_ = v_reuseFailAlloc_6706_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6705_;
            }
            6 => {
                if v_isShared_6715_ == 0 {
                    v___x_6717_ = v___x_6714_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6718_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6718_, 0, v_a_6712_);
                    v___x_6717_ = v_reuseFailAlloc_6718_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6717_;
            }
            8 => {
                if v_isShared_6728_ == 0 {
                    v___x_6730_ = v___x_6727_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6731_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6731_, 0, v_a_6725_);
                    v___x_6730_ = v_reuseFailAlloc_6731_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6730_;
            }
            10 => {
                if v_isShared_6736_ == 0 {
                    v___x_6738_ = v___x_6735_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6739_, 0, v_a_6733_);
                    v___x_6738_ = v_reuseFailAlloc_6739_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6738_;
            }
            12 => {
                if v_isShared_6744_ == 0 {
                    v___x_6746_ = v___x_6743_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6747_, 0, v_a_6741_);
                    v___x_6746_ = v_reuseFailAlloc_6747_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6746_;
            }
            14 => {
                if v_isShared_6753_ == 0 {
                    v___x_6755_ = v___x_6752_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6756_, 0, v_a_6750_);
                    v___x_6755_ = v_reuseFailAlloc_6756_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6755_;
            }
            16 => {
                if v_isShared_6761_ == 0 {
                    v___x_6763_ = v___x_6760_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6764_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6764_, 0, v_a_6758_);
                    v___x_6763_ = v_reuseFailAlloc_6764_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6763_;
            }
            18 => {
                if v_isShared_6769_ == 0 {
                    v___x_6771_ = v___x_6768_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6772_, 0, v_a_6766_);
                    v___x_6771_ = v_reuseFailAlloc_6772_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_instantiate_x27___boxed(
    mut v_goal_6774_: *mut crate::leanh::LeanObject,
    mut v_kna_6775_: *mut crate::leanh::LeanObject,
    mut v_kp_6776_: *mut crate::leanh::LeanObject,
    mut v_a_6777_: *mut crate::leanh::LeanObject,
    mut v_a_6778_: *mut crate::leanh::LeanObject,
    mut v_a_6779_: *mut crate::leanh::LeanObject,
    mut v_a_6780_: *mut crate::leanh::LeanObject,
    mut v_a_6781_: *mut crate::leanh::LeanObject,
    mut v_a_6782_: *mut crate::leanh::LeanObject,
    mut v_a_6783_: *mut crate::leanh::LeanObject,
    mut v_a_6784_: *mut crate::leanh::LeanObject,
    mut v_a_6785_: *mut crate::leanh::LeanObject,
    mut v_a_6786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6787_ = l_Lean_Meta_Grind_Action_instantiate_x27(
        v_goal_6774_,
        v_kna_6775_,
        v_kp_6776_,
        v_a_6777_,
        v_a_6778_,
        v_a_6779_,
        v_a_6780_,
        v_a_6781_,
        v_a_6782_,
        v_a_6783_,
        v_a_6784_,
        v_a_6785_,
    );
    crate::leanh::lean_dec(v_a_6785_);
    crate::leanh::lean_dec_ref(v_a_6784_);
    crate::leanh::lean_dec(v_a_6783_);
    crate::leanh::lean_dec_ref(v_a_6782_);
    crate::leanh::lean_dec(v_a_6781_);
    crate::leanh::lean_dec_ref(v_a_6780_);
    crate::leanh::lean_dec(v_a_6779_);
    crate::leanh::lean_dec_ref(v_a_6778_);
    crate::leanh::lean_dec(v_a_6777_);
    return v_res_6787_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__4(
    mut v_i_6788_: *mut crate::leanh::LeanObject,
    mut v_a_6789_: *mut crate::leanh::LeanObject,
    mut v_a_6790_: *mut crate::leanh::LeanObject,
    mut v___y_6791_: *mut crate::leanh::LeanObject,
    mut v___y_6792_: *mut crate::leanh::LeanObject,
    mut v___y_6793_: *mut crate::leanh::LeanObject,
    mut v___y_6794_: *mut crate::leanh::LeanObject,
    mut v___y_6795_: *mut crate::leanh::LeanObject,
    mut v___y_6796_: *mut crate::leanh::LeanObject,
    mut v___y_6797_: *mut crate::leanh::LeanObject,
    mut v___y_6798_: *mut crate::leanh::LeanObject,
    mut v___y_6799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6801_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__4___redArg(v_i_6788_, v_a_6790_);
    return v___x_6801_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_i_6802_: *mut crate::leanh::LeanObject,
    mut v_a_6803_: *mut crate::leanh::LeanObject,
    mut v_a_6804_: *mut crate::leanh::LeanObject,
    mut v___y_6805_: *mut crate::leanh::LeanObject,
    mut v___y_6806_: *mut crate::leanh::LeanObject,
    mut v___y_6807_: *mut crate::leanh::LeanObject,
    mut v___y_6808_: *mut crate::leanh::LeanObject,
    mut v___y_6809_: *mut crate::leanh::LeanObject,
    mut v___y_6810_: *mut crate::leanh::LeanObject,
    mut v___y_6811_: *mut crate::leanh::LeanObject,
    mut v___y_6812_: *mut crate::leanh::LeanObject,
    mut v___y_6813_: *mut crate::leanh::LeanObject,
    mut v___y_6814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6815_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__4(v_i_6802_, v_a_6803_, v_a_6804_, v___y_6805_, v___y_6806_, v___y_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_, v___y_6812_, v___y_6813_);
    crate::leanh::lean_dec(v___y_6813_);
    crate::leanh::lean_dec_ref(v___y_6812_);
    crate::leanh::lean_dec(v___y_6811_);
    crate::leanh::lean_dec_ref(v___y_6810_);
    crate::leanh::lean_dec(v___y_6809_);
    crate::leanh::lean_dec_ref(v___y_6808_);
    crate::leanh::lean_dec(v___y_6807_);
    crate::leanh::lean_dec_ref(v___y_6806_);
    crate::leanh::lean_dec(v___y_6805_);
    crate::leanh::lean_dec_ref(v_a_6803_);
    return v_res_6815_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__7(
    mut v_i_6816_: *mut crate::leanh::LeanObject,
    mut v_a_6817_: *mut crate::leanh::LeanObject,
    mut v_a_6818_: *mut crate::leanh::LeanObject,
    mut v___y_6819_: *mut crate::leanh::LeanObject,
    mut v___y_6820_: *mut crate::leanh::LeanObject,
    mut v___y_6821_: *mut crate::leanh::LeanObject,
    mut v___y_6822_: *mut crate::leanh::LeanObject,
    mut v___y_6823_: *mut crate::leanh::LeanObject,
    mut v___y_6824_: *mut crate::leanh::LeanObject,
    mut v___y_6825_: *mut crate::leanh::LeanObject,
    mut v___y_6826_: *mut crate::leanh::LeanObject,
    mut v___y_6827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6829_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__7___redArg(v_i_6816_, v_a_6818_);
    return v___x_6829_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__7___boxed(
    mut v_i_6830_: *mut crate::leanh::LeanObject,
    mut v_a_6831_: *mut crate::leanh::LeanObject,
    mut v_a_6832_: *mut crate::leanh::LeanObject,
    mut v___y_6833_: *mut crate::leanh::LeanObject,
    mut v___y_6834_: *mut crate::leanh::LeanObject,
    mut v___y_6835_: *mut crate::leanh::LeanObject,
    mut v___y_6836_: *mut crate::leanh::LeanObject,
    mut v___y_6837_: *mut crate::leanh::LeanObject,
    mut v___y_6838_: *mut crate::leanh::LeanObject,
    mut v___y_6839_: *mut crate::leanh::LeanObject,
    mut v___y_6840_: *mut crate::leanh::LeanObject,
    mut v___y_6841_: *mut crate::leanh::LeanObject,
    mut v___y_6842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6843_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__7(v_i_6830_, v_a_6831_, v_a_6832_, v___y_6833_, v___y_6834_, v___y_6835_, v___y_6836_, v___y_6837_, v___y_6838_, v___y_6839_, v___y_6840_, v___y_6841_);
    crate::leanh::lean_dec(v___y_6841_);
    crate::leanh::lean_dec_ref(v___y_6840_);
    crate::leanh::lean_dec(v___y_6839_);
    crate::leanh::lean_dec_ref(v___y_6838_);
    crate::leanh::lean_dec(v___y_6837_);
    crate::leanh::lean_dec_ref(v___y_6836_);
    crate::leanh::lean_dec(v___y_6835_);
    crate::leanh::lean_dec_ref(v___y_6834_);
    crate::leanh::lean_dec(v___y_6833_);
    crate::leanh::lean_dec_ref(v_a_6831_);
    crate::leanh::lean_dec(v_i_6830_);
    return v_res_6843_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__8(
    mut v_i_6844_: *mut crate::leanh::LeanObject,
    mut v_a_6845_: *mut crate::leanh::LeanObject,
    mut v_a_6846_: *mut crate::leanh::LeanObject,
    mut v___y_6847_: *mut crate::leanh::LeanObject,
    mut v___y_6848_: *mut crate::leanh::LeanObject,
    mut v___y_6849_: *mut crate::leanh::LeanObject,
    mut v___y_6850_: *mut crate::leanh::LeanObject,
    mut v___y_6851_: *mut crate::leanh::LeanObject,
    mut v___y_6852_: *mut crate::leanh::LeanObject,
    mut v___y_6853_: *mut crate::leanh::LeanObject,
    mut v___y_6854_: *mut crate::leanh::LeanObject,
    mut v___y_6855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6857_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__8___redArg(v_i_6844_, v_a_6846_);
    return v___x_6857_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__8___boxed(
    mut v_i_6858_: *mut crate::leanh::LeanObject,
    mut v_a_6859_: *mut crate::leanh::LeanObject,
    mut v_a_6860_: *mut crate::leanh::LeanObject,
    mut v___y_6861_: *mut crate::leanh::LeanObject,
    mut v___y_6862_: *mut crate::leanh::LeanObject,
    mut v___y_6863_: *mut crate::leanh::LeanObject,
    mut v___y_6864_: *mut crate::leanh::LeanObject,
    mut v___y_6865_: *mut crate::leanh::LeanObject,
    mut v___y_6866_: *mut crate::leanh::LeanObject,
    mut v___y_6867_: *mut crate::leanh::LeanObject,
    mut v___y_6868_: *mut crate::leanh::LeanObject,
    mut v___y_6869_: *mut crate::leanh::LeanObject,
    mut v___y_6870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6871_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__8(v_i_6858_, v_a_6859_, v_a_6860_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_, v___y_6867_, v___y_6868_, v___y_6869_);
    crate::leanh::lean_dec(v___y_6869_);
    crate::leanh::lean_dec_ref(v___y_6868_);
    crate::leanh::lean_dec(v___y_6867_);
    crate::leanh::lean_dec_ref(v___y_6866_);
    crate::leanh::lean_dec(v___y_6865_);
    crate::leanh::lean_dec_ref(v___y_6864_);
    crate::leanh::lean_dec(v___y_6863_);
    crate::leanh::lean_dec_ref(v___y_6862_);
    crate::leanh::lean_dec(v___y_6861_);
    crate::leanh::lean_dec_ref(v_a_6859_);
    crate::leanh::lean_dec(v_i_6858_);
    return v_res_6871_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4(
    mut v_a_6872_: *mut crate::leanh::LeanObject,
    mut v_a_6873_: *mut crate::leanh::LeanObject,
    mut v___y_6874_: *mut crate::leanh::LeanObject,
    mut v___y_6875_: *mut crate::leanh::LeanObject,
    mut v___y_6876_: *mut crate::leanh::LeanObject,
    mut v___y_6877_: *mut crate::leanh::LeanObject,
    mut v___y_6878_: *mut crate::leanh::LeanObject,
    mut v___y_6879_: *mut crate::leanh::LeanObject,
    mut v___y_6880_: *mut crate::leanh::LeanObject,
    mut v___y_6881_: *mut crate::leanh::LeanObject,
    mut v___y_6882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6884_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___redArg(v_a_6873_);
    return v___x_6884_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_a_6885_: *mut crate::leanh::LeanObject,
    mut v_a_6886_: *mut crate::leanh::LeanObject,
    mut v___y_6887_: *mut crate::leanh::LeanObject,
    mut v___y_6888_: *mut crate::leanh::LeanObject,
    mut v___y_6889_: *mut crate::leanh::LeanObject,
    mut v___y_6890_: *mut crate::leanh::LeanObject,
    mut v___y_6891_: *mut crate::leanh::LeanObject,
    mut v___y_6892_: *mut crate::leanh::LeanObject,
    mut v___y_6893_: *mut crate::leanh::LeanObject,
    mut v___y_6894_: *mut crate::leanh::LeanObject,
    mut v___y_6895_: *mut crate::leanh::LeanObject,
    mut v___y_6896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6897_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__3_spec__4(v_a_6885_, v_a_6886_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_, v___y_6893_, v___y_6894_, v___y_6895_);
    crate::leanh::lean_dec(v___y_6895_);
    crate::leanh::lean_dec_ref(v___y_6894_);
    crate::leanh::lean_dec(v___y_6893_);
    crate::leanh::lean_dec_ref(v___y_6892_);
    crate::leanh::lean_dec(v___y_6891_);
    crate::leanh::lean_dec_ref(v___y_6890_);
    crate::leanh::lean_dec(v___y_6889_);
    crate::leanh::lean_dec_ref(v___y_6888_);
    crate::leanh::lean_dec(v___y_6887_);
    crate::leanh::lean_dec_ref(v_a_6885_);
    return v_res_6897_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5(
    mut v_upperBound_6898_: *mut crate::leanh::LeanObject,
    mut v___x_6899_: *mut crate::leanh::LeanObject,
    mut v_inst_6900_: *mut crate::leanh::LeanObject,
    mut v_R_6901_: *mut crate::leanh::LeanObject,
    mut v_a_6902_: *mut crate::leanh::LeanObject,
    mut v_b_6903_: *mut crate::leanh::LeanObject,
    mut v_c_6904_: *mut crate::leanh::LeanObject,
    mut v___y_6905_: *mut crate::leanh::LeanObject,
    mut v___y_6906_: *mut crate::leanh::LeanObject,
    mut v___y_6907_: *mut crate::leanh::LeanObject,
    mut v___y_6908_: *mut crate::leanh::LeanObject,
    mut v___y_6909_: *mut crate::leanh::LeanObject,
    mut v___y_6910_: *mut crate::leanh::LeanObject,
    mut v___y_6911_: *mut crate::leanh::LeanObject,
    mut v___y_6912_: *mut crate::leanh::LeanObject,
    mut v___y_6913_: *mut crate::leanh::LeanObject,
    mut v___y_6914_: *mut crate::leanh::LeanObject,
    mut v___y_6915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6917_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___redArg(v_upperBound_6898_, v___x_6899_, v_a_6902_, v_b_6903_, v___y_6905_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_, v___y_6910_, v___y_6911_, v___y_6912_, v___y_6913_, v___y_6914_, v___y_6915_);
    return v___x_6917_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_6918_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_6919_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_inst_6920_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_R_6921_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_6922_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_6923_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_c_6924_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_6925_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_6926_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_6927_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_6928_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_6929_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_6930_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6931_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6932_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6933_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6934_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6935_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_6936_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__2_spec__5(v_upperBound_6918_, v___x_6919_, v_inst_6920_, v_R_6921_, v_a_6922_, v_b_6923_, v_c_6924_, v___y_6925_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_, v___y_6932_, v___y_6933_, v___y_6934_, v___y_6935_);
    crate::leanh::lean_dec(v___y_6935_);
    crate::leanh::lean_dec_ref(v___y_6934_);
    crate::leanh::lean_dec(v___y_6933_);
    crate::leanh::lean_dec_ref(v___y_6932_);
    crate::leanh::lean_dec(v___y_6931_);
    crate::leanh::lean_dec_ref(v___y_6930_);
    crate::leanh::lean_dec(v___y_6929_);
    crate::leanh::lean_dec_ref(v___y_6928_);
    crate::leanh::lean_dec(v___y_6927_);
    crate::leanh::lean_dec_ref(v___y_6925_);
    crate::leanh::lean_dec_ref(v___x_6919_);
    crate::leanh::lean_dec(v_upperBound_6918_);
    return v_res_6937_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9(
    mut v_inst_6938_: *mut crate::leanh::LeanObject,
    mut v_a_6939_: *mut crate::leanh::LeanObject,
    mut v___y_6940_: *mut crate::leanh::LeanObject,
    mut v___y_6941_: *mut crate::leanh::LeanObject,
    mut v___y_6942_: *mut crate::leanh::LeanObject,
    mut v___y_6943_: *mut crate::leanh::LeanObject,
    mut v___y_6944_: *mut crate::leanh::LeanObject,
    mut v___y_6945_: *mut crate::leanh::LeanObject,
    mut v___y_6946_: *mut crate::leanh::LeanObject,
    mut v___y_6947_: *mut crate::leanh::LeanObject,
    mut v___y_6948_: *mut crate::leanh::LeanObject,
    mut v___y_6949_: *mut crate::leanh::LeanObject,
    mut v___y_6950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6952_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___redArg(v_a_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_, v___y_6948_, v___y_6949_, v___y_6950_);
    return v___x_6952_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9___boxed(
    mut v_inst_6953_: *mut crate::leanh::LeanObject,
    mut v_a_6954_: *mut crate::leanh::LeanObject,
    mut v___y_6955_: *mut crate::leanh::LeanObject,
    mut v___y_6956_: *mut crate::leanh::LeanObject,
    mut v___y_6957_: *mut crate::leanh::LeanObject,
    mut v___y_6958_: *mut crate::leanh::LeanObject,
    mut v___y_6959_: *mut crate::leanh::LeanObject,
    mut v___y_6960_: *mut crate::leanh::LeanObject,
    mut v___y_6961_: *mut crate::leanh::LeanObject,
    mut v___y_6962_: *mut crate::leanh::LeanObject,
    mut v___y_6963_: *mut crate::leanh::LeanObject,
    mut v___y_6964_: *mut crate::leanh::LeanObject,
    mut v___y_6965_: *mut crate::leanh::LeanObject,
    mut v___y_6966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6967_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___at___00__private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___at___00Lean_Util_ParamMinimizer_search___at___00Lean_Meta_Grind_Action_instantiate_x27_spec__1_spec__1_spec__3_spec__9(v_inst_6953_, v_a_6954_, v___y_6955_, v___y_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_, v___y_6961_, v___y_6962_, v___y_6963_, v___y_6964_, v___y_6965_);
    crate::leanh::lean_dec(v___y_6965_);
    crate::leanh::lean_dec_ref(v___y_6964_);
    crate::leanh::lean_dec(v___y_6963_);
    crate::leanh::lean_dec_ref(v___y_6962_);
    crate::leanh::lean_dec(v___y_6961_);
    crate::leanh::lean_dec_ref(v___y_6960_);
    crate::leanh::lean_dec(v___y_6959_);
    crate::leanh::lean_dec_ref(v___y_6958_);
    crate::leanh::lean_dec(v___y_6957_);
    crate::leanh::lean_dec_ref(v___y_6955_);
    return v_res_6967_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instantiate___lam__0(
    mut v___y_6968_: *mut crate::leanh::LeanObject,
    mut v___y_6969_: *mut crate::leanh::LeanObject,
    mut v___y_6970_: *mut crate::leanh::LeanObject,
    mut v___y_6971_: *mut crate::leanh::LeanObject,
    mut v___y_6972_: *mut crate::leanh::LeanObject,
    mut v___y_6973_: *mut crate::leanh::LeanObject,
    mut v___y_6974_: *mut crate::leanh::LeanObject,
    mut v___y_6975_: *mut crate::leanh::LeanObject,
    mut v___y_6976_: *mut crate::leanh::LeanObject,
    mut v___y_6977_: *mut crate::leanh::LeanObject,
    mut v___y_6978_: *mut crate::leanh::LeanObject,
    mut v___y_6979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6981_ = l_Lean_Meta_Grind_Action_assertAll___redArg(
        v___y_6968_,
        v___y_6970_,
        v___y_6971_,
        v___y_6972_,
        v___y_6973_,
        v___y_6974_,
        v___y_6975_,
        v___y_6976_,
        v___y_6977_,
        v___y_6978_,
        v___y_6979_,
    );
    return v___x_6981_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instantiate___lam__0___boxed(
    mut v___y_6982_: *mut crate::leanh::LeanObject,
    mut v___y_6983_: *mut crate::leanh::LeanObject,
    mut v___y_6984_: *mut crate::leanh::LeanObject,
    mut v___y_6985_: *mut crate::leanh::LeanObject,
    mut v___y_6986_: *mut crate::leanh::LeanObject,
    mut v___y_6987_: *mut crate::leanh::LeanObject,
    mut v___y_6988_: *mut crate::leanh::LeanObject,
    mut v___y_6989_: *mut crate::leanh::LeanObject,
    mut v___y_6990_: *mut crate::leanh::LeanObject,
    mut v___y_6991_: *mut crate::leanh::LeanObject,
    mut v___y_6992_: *mut crate::leanh::LeanObject,
    mut v___y_6993_: *mut crate::leanh::LeanObject,
    mut v___y_6994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6995_ = l_Lean_Meta_Grind_Action_instantiate___lam__0(
        v___y_6982_,
        v___y_6983_,
        v___y_6984_,
        v___y_6985_,
        v___y_6986_,
        v___y_6987_,
        v___y_6988_,
        v___y_6989_,
        v___y_6990_,
        v___y_6991_,
        v___y_6992_,
        v___y_6993_,
    );
    crate::leanh::lean_dec(v___y_6993_);
    crate::leanh::lean_dec_ref(v___y_6992_);
    crate::leanh::lean_dec(v___y_6991_);
    crate::leanh::lean_dec_ref(v___y_6990_);
    crate::leanh::lean_dec(v___y_6989_);
    crate::leanh::lean_dec_ref(v___y_6988_);
    crate::leanh::lean_dec(v___y_6987_);
    crate::leanh::lean_dec_ref(v___y_6986_);
    crate::leanh::lean_dec(v___y_6985_);
    crate::leanh::lean_dec_ref(v___y_6983_);
    return v_res_6995_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instantiate(
    mut v_a_6997_: *mut crate::leanh::LeanObject,
    mut v_kna_6998_: *mut crate::leanh::LeanObject,
    mut v_kp_6999_: *mut crate::leanh::LeanObject,
    mut v_a_7000_: *mut crate::leanh::LeanObject,
    mut v_a_7001_: *mut crate::leanh::LeanObject,
    mut v_a_7002_: *mut crate::leanh::LeanObject,
    mut v_a_7003_: *mut crate::leanh::LeanObject,
    mut v_a_7004_: *mut crate::leanh::LeanObject,
    mut v_a_7005_: *mut crate::leanh::LeanObject,
    mut v_a_7006_: *mut crate::leanh::LeanObject,
    mut v_a_7007_: *mut crate::leanh::LeanObject,
    mut v_a_7008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_7010_ = l_Lean_Meta_Grind_Action_instantiate___closed__0;
    v___x_7011_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Action_instantiate_x27___boxed as *mut core::ffi::c_void,
        13,
        0,
    );
    v___x_7012_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_7011_,
        v___f_7010_,
        v_a_6997_,
        v_kna_6998_,
        v_kp_6999_,
        v_a_7000_,
        v_a_7001_,
        v_a_7002_,
        v_a_7003_,
        v_a_7004_,
        v_a_7005_,
        v_a_7006_,
        v_a_7007_,
        v_a_7008_,
    );
    return v___x_7012_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_instantiate___boxed(
    mut v_a_7013_: *mut crate::leanh::LeanObject,
    mut v_kna_7014_: *mut crate::leanh::LeanObject,
    mut v_kp_7015_: *mut crate::leanh::LeanObject,
    mut v_a_7016_: *mut crate::leanh::LeanObject,
    mut v_a_7017_: *mut crate::leanh::LeanObject,
    mut v_a_7018_: *mut crate::leanh::LeanObject,
    mut v_a_7019_: *mut crate::leanh::LeanObject,
    mut v_a_7020_: *mut crate::leanh::LeanObject,
    mut v_a_7021_: *mut crate::leanh::LeanObject,
    mut v_a_7022_: *mut crate::leanh::LeanObject,
    mut v_a_7023_: *mut crate::leanh::LeanObject,
    mut v_a_7024_: *mut crate::leanh::LeanObject,
    mut v_a_7025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7026_ = l_Lean_Meta_Grind_Action_instantiate(
        v_a_7013_,
        v_kna_7014_,
        v_kp_7015_,
        v_a_7016_,
        v_a_7017_,
        v_a_7018_,
        v_a_7019_,
        v_a_7020_,
        v_a_7021_,
        v_a_7022_,
        v_a_7023_,
        v_a_7024_,
    );
    crate::leanh::lean_dec(v_a_7024_);
    crate::leanh::lean_dec_ref(v_a_7023_);
    crate::leanh::lean_dec(v_a_7022_);
    crate::leanh::lean_dec_ref(v_a_7021_);
    crate::leanh::lean_dec(v_a_7020_);
    crate::leanh::lean_dec_ref(v_a_7019_);
    crate::leanh::lean_dec(v_a_7018_);
    crate::leanh::lean_dec_ref(v_a_7017_);
    crate::leanh::lean_dec(v_a_7016_);
    return v_res_7026_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ParamMinimizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_EMatchAction(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_EMatchAction(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_ParamMinimizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EMatchTheoremPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
}
