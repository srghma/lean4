// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.PropagateInj
// Imports: Lean.Meta.Tactic.Grind.Types Init.Grind.Propagator Init.Grind.Injective Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Simp
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_grind_internalize, lean_mk_array, lean_nat_add,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Grind::Injective::{
    initialize_Init_Grind_Injective, runtime_initialize_Init_Grind_Injective,
};
use crate::r#gen::Init::Grind::Propagator::{
    initialize_Init_Grind_Propagator, runtime_initialize_Init_Grind_Propagator,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_eta, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_Expr_sort___override, l_Lean_mkApp5, l_Lean_mkAppB,
    l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::HeadIndex::{
    l_Lean_Expr_toHeadIndex, l_Lean_HeadIndex_hash, l_Lean_instBEqHeadIndex_beq,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkOfEqTrueCore;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::PropagatorAttr::{
    initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
    l_Lean_Meta_Grind_registerBuiltinDownwardPropagator,
    runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Simp::{
    initialize_Lean_Meta_Tactic_Grind_Simp, l_Lean_Meta_Grind_preprocessLight___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_getGeneration___redArg,
    l_Lean_Meta_Grind_instInhabitedGoalM, l_Lean_Meta_Grind_isEqTrue___redArg,
    l_Lean_Meta_Grind_mkEqTrueProof, l_Lean_Meta_Grind_pushEqCore___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 73, 110, 106, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1_value: crate::leanh::LeanStringObject<74> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 73, 110, 106, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 103, 101, 116, 73, 110, 118, 70, 111, 114, 63, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 110, 116, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4_value) as *mut crate::leanh::LeanObject,13229434762204987278 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5_value) as *mut crate::leanh::LeanObject,7945323172821520753 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 102, 116, 73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9_value) as *mut crate::leanh::LeanObject,4547445378961686909 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 101, 102, 116, 73, 110, 118, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12_value) as *mut crate::leanh::LeanObject,11626608933517746935 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2_value:
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
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkInjEq___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_mkInjEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkInjEq___closed__1_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 110, 106, 0],
    };
static mut l_Lean_Meta_Grind_mkInjEq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkInjEq___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [97, 115, 115, 101, 114, 116, 0],
    };
static mut l_Lean_Meta_Grind_mkInjEq___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15947788021050471391 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__1_value)
                as *mut crate::leanh::LeanObject,
            1891887995088964530 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_mkInjEq___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16986677381411493332 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkInjEq___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkInjEq___closed__4_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_mkInjEq___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkInjEq___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__4_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkInjEq___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkInjEq___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkInjEq___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkInjEq___closed__7_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkInjEq___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkInjEq___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkInjEq___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [70, 117, 110, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 106, 101, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0_value) as *mut crate::leanh::LeanObject,920240211420121313 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1_value) as *mut crate::leanh::LeanObject,14487767036850709044 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1129_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_1129_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(
    mut v_msg_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
    mut v___y_1136_: *mut crate::leanh::LeanObject,
    mut v___y_1137_: *mut crate::leanh::LeanObject,
    mut v___y_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9023__overap_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1142_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0);
    v___x_9023__overap_1143_ = lean_panic_fn_borrowed(v___x_1142_, v_msg_1130_);
    crate::leanh::lean_inc(v___y_1140_);
    crate::leanh::lean_inc_ref(v___y_1139_);
    crate::leanh::lean_inc(v___y_1138_);
    crate::leanh::lean_inc_ref(v___y_1137_);
    crate::leanh::lean_inc(v___y_1136_);
    crate::leanh::lean_inc_ref(v___y_1135_);
    crate::leanh::lean_inc(v___y_1134_);
    crate::leanh::lean_inc_ref(v___y_1133_);
    crate::leanh::lean_inc(v___y_1132_);
    crate::leanh::lean_inc(v___y_1131_);
    v___x_1144_ = crate::leanh::lean_apply_11(
        v___x_9023__overap_1143_,
        v___y_1131_,
        v___y_1132_,
        v___y_1133_,
        v___y_1134_,
        v___y_1135_,
        v___y_1136_,
        v___y_1137_,
        v___y_1138_,
        v___y_1139_,
        v___y_1140_,
        crate::leanh::lean_box(0),
    );
    return v___x_1144_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___boxed(
    mut v_msg_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
    mut v___y_1149_: *mut crate::leanh::LeanObject,
    mut v___y_1150_: *mut crate::leanh::LeanObject,
    mut v___y_1151_: *mut crate::leanh::LeanObject,
    mut v___y_1152_: *mut crate::leanh::LeanObject,
    mut v___y_1153_: *mut crate::leanh::LeanObject,
    mut v___y_1154_: *mut crate::leanh::LeanObject,
    mut v___y_1155_: *mut crate::leanh::LeanObject,
    mut v___y_1156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1157_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v_msg_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
    crate::leanh::lean_dec(v___y_1155_);
    crate::leanh::lean_dec_ref(v___y_1154_);
    crate::leanh::lean_dec(v___y_1153_);
    crate::leanh::lean_dec_ref(v___y_1152_);
    crate::leanh::lean_dec(v___y_1151_);
    crate::leanh::lean_dec_ref(v___y_1150_);
    crate::leanh::lean_dec(v___y_1149_);
    crate::leanh::lean_dec_ref(v___y_1148_);
    crate::leanh::lean_dec(v___y_1147_);
    crate::leanh::lean_dec(v___y_1146_);
    return v_res_1157_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(
    mut v_keys_1158_: *mut crate::leanh::LeanObject,
    mut v_vals_1159_: *mut crate::leanh::LeanObject,
    mut v_i_1160_: *mut crate::leanh::LeanObject,
    mut v_k_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1162_ = lean_array_get_size(v_keys_1158_);
                v___x_1163_ = lean_nat_dec_lt(v_i_1160_, v___x_1162_);
                if v___x_1163_ == 0 {
                    crate::leanh::lean_dec(v_i_1160_);
                    v___x_1164_ = crate::leanh::lean_box(0);
                    return v___x_1164_;
                } else {
                    v_k_x27_1165_ = lean_array_fget_borrowed(v_keys_1158_, v_i_1160_);
                    v___x_1166_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1161_,
                            v_k_x27_1165_,
                        );
                    if v___x_1166_ == 0 {
                        v___x_1167_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1168_ = lean_nat_add(v_i_1160_, v___x_1167_);
                        crate::leanh::lean_dec(v_i_1160_);
                        v_i_1160_ = v___x_1168_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1170_ = lean_array_fget_borrowed(v_vals_1159_, v_i_1160_);
                        crate::leanh::lean_dec(v_i_1160_);
                        crate::leanh::lean_inc(v___x_1170_);
                        v___x_1171_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1171_, 0, v___x_1170_);
                        return v___x_1171_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_keys_1172_: *mut crate::leanh::LeanObject,
    mut v_vals_1173_: *mut crate::leanh::LeanObject,
    mut v_i_1174_: *mut crate::leanh::LeanObject,
    mut v_k_1175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1176_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_1172_, v_vals_1173_, v_i_1174_, v_k_1175_);
    crate::leanh::lean_dec_ref(v_k_1175_);
    crate::leanh::lean_dec_ref(v_vals_1173_);
    crate::leanh::lean_dec_ref(v_keys_1172_);
    return v_res_1176_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_1177_: usize = 0;
    let mut v___x_1178_: usize = 0;
    let mut v___x_1179_: usize = 0;
    v___x_1177_ = 5usize;
    v___x_1178_ = 1usize;
    v___x_1179_ = lean_usize_shift_left(v___x_1178_, v___x_1177_);
    return v___x_1179_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_1180_: usize = 0;
    let mut v___x_1181_: usize = 0;
    let mut v___x_1182_: usize = 0;
    v___x_1180_ = 1usize;
    v___x_1181_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0);
    v___x_1182_ = lean_usize_sub(v___x_1181_, v___x_1180_);
    return v___x_1182_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(
    mut v_x_1183_: *mut crate::leanh::LeanObject,
    mut v_x_1184_: usize,
    mut v_x_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: usize = 0;
    let mut v___x_1189_: usize = 0;
    let mut v___x_1190_: usize = 0;
    let mut v_j_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: usize = 0;
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1183_) == 0 {
                    v_es_1186_ = crate::leanh::lean_ctor_get(v_x_1183_, 0);
                    v___x_1187_ = crate::leanh::lean_box(2);
                    v___x_1188_ = 5usize;
                    v___x_1189_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
                    v___x_1190_ = lean_usize_land(v_x_1184_, v___x_1189_);
                    v_j_1191_ = lean_usize_to_nat(v___x_1190_);
                    v___x_1192_ = lean_array_get_borrowed(v___x_1187_, v_es_1186_, v_j_1191_);
                    crate::leanh::lean_dec(v_j_1191_);
                    match crate::leanh::lean_obj_tag(v___x_1192_) {
                        0 => {
                            v_key_1193_ = crate::leanh::lean_ctor_get(v___x_1192_, 0);
                            v_val_1194_ = crate::leanh::lean_ctor_get(v___x_1192_, 1);
                            v___x_1195_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1185_, v_key_1193_);
                            if v___x_1195_ == 0 {
                                v___x_1196_ = crate::leanh::lean_box(0);
                                return v___x_1196_;
                            } else {
                                crate::leanh::lean_inc(v_val_1194_);
                                v___x_1197_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1197_, 0, v_val_1194_);
                                return v___x_1197_;
                            }
                        }
                        1 => {
                            v_node_1198_ = crate::leanh::lean_ctor_get(v___x_1192_, 0);
                            v___x_1199_ = lean_usize_shift_right(v_x_1184_, v___x_1188_);
                            v_x_1183_ = v_node_1198_;
                            v_x_1184_ = v___x_1199_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1201_ = crate::leanh::lean_box(0);
                            return v___x_1201_;
                        }
                    }
                } else {
                    v_ks_1202_ = crate::leanh::lean_ctor_get(v_x_1183_, 0);
                    v_vs_1203_ = crate::leanh::lean_ctor_get(v_x_1183_, 1);
                    v___x_1204_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1205_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_ks_1202_, v_vs_1203_, v___x_1204_, v_x_1185_);
                    return v___x_1205_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___boxed(
    mut v_x_1206_: *mut crate::leanh::LeanObject,
    mut v_x_1207_: *mut crate::leanh::LeanObject,
    mut v_x_1208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9505__boxed_1209_: usize = 0;
    let mut v_res_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9505__boxed_1209_ = crate::leanh::lean_unbox_usize(v_x_1207_);
    crate::leanh::lean_dec(v_x_1207_);
    v_res_1210_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_1206_, v_x_9505__boxed_1209_, v_x_1208_);
    crate::leanh::lean_dec_ref(v_x_1208_);
    crate::leanh::lean_dec_ref(v_x_1206_);
    return v_res_1210_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(
    mut v_x_1211_: *mut crate::leanh::LeanObject,
    mut v_x_1212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1213_: u64 = 0;
    let mut v___x_1214_: usize = 0;
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1213_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1212_);
    v___x_1214_ = lean_uint64_to_usize(v___x_1213_);
    v___x_1215_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_1211_, v___x_1214_, v_x_1212_);
    return v___x_1215_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg___boxed(
    mut v_x_1216_: *mut crate::leanh::LeanObject,
    mut v_x_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1218_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_1216_, v_x_1217_);
    crate::leanh::lean_dec_ref(v_x_1217_);
    crate::leanh::lean_dec_ref(v_x_1216_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(
    mut v_x_1219_: *mut crate::leanh::LeanObject,
    mut v_x_1220_: *mut crate::leanh::LeanObject,
    mut v_x_1221_: *mut crate::leanh::LeanObject,
    mut v_x_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: u8 = 0;
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1223_ = crate::leanh::lean_ctor_get(v_x_1219_, 0);
                v_vs_1224_ = crate::leanh::lean_ctor_get(v_x_1219_, 1);
                v_isSharedCheck_1248_ = (!crate::leanh::lean_is_exclusive(v_x_1219_)) as u8;
                if v_isSharedCheck_1248_ == 0 {
                    v___x_1226_ = v_x_1219_;
                    v_isShared_1227_ = v_isSharedCheck_1248_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1224_);
                    crate::leanh::lean_inc(v_ks_1223_);
                    crate::leanh::lean_dec(v_x_1219_);
                    v___x_1226_ = crate::leanh::lean_box(0);
                    v_isShared_1227_ = v_isSharedCheck_1248_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1228_ = lean_array_get_size(v_ks_1223_);
                v___x_1229_ = lean_nat_dec_lt(v_x_1220_, v___x_1228_);
                if v___x_1229_ == 0 {
                    crate::leanh::lean_dec(v_x_1220_);
                    v___x_1230_ = lean_array_push(v_ks_1223_, v_x_1221_);
                    v___x_1231_ = lean_array_push(v_vs_1224_, v_x_1222_);
                    if v_isShared_1227_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1226_, 1, v___x_1231_);
                        crate::leanh::lean_ctor_set(v___x_1226_, 0, v___x_1230_);
                        v___x_1233_ = v___x_1226_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1234_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1230_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1231_);
                        v___x_1233_ = v_reuseFailAlloc_1234_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1235_ = lean_array_fget_borrowed(v_ks_1223_, v_x_1220_);
                    v___x_1236_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_1221_,
                            v_k_x27_1235_,
                        );
                    if v___x_1236_ == 0 {
                        if v_isShared_1227_ == 0 {
                            v___x_1238_ = v___x_1226_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1242_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_ks_1223_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_vs_1224_);
                            v___x_1238_ = v_reuseFailAlloc_1242_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1243_ = lean_array_fset(v_ks_1223_, v_x_1220_, v_x_1221_);
                        v___x_1244_ = lean_array_fset(v_vs_1224_, v_x_1220_, v_x_1222_);
                        crate::leanh::lean_dec(v_x_1220_);
                        if v_isShared_1227_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1226_, 1, v___x_1244_);
                            crate::leanh::lean_ctor_set(v___x_1226_, 0, v___x_1243_);
                            v___x_1246_ = v___x_1226_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1247_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1243_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1244_);
                            v___x_1246_ = v_reuseFailAlloc_1247_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1233_;
            }
            3 => {
                v___x_1239_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1240_ = lean_nat_add(v_x_1220_, v___x_1239_);
                crate::leanh::lean_dec(v_x_1220_);
                v_x_1219_ = v___x_1238_;
                v_x_1220_ = v___x_1240_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(
    mut v_n_1249_: *mut crate::leanh::LeanObject,
    mut v_k_1250_: *mut crate::leanh::LeanObject,
    mut v_v_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1253_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_n_1249_, v___x_1252_, v_k_1250_, v_v_1251_);
    return v___x_1253_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1254_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1254_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(
    mut v_x_1255_: *mut crate::leanh::LeanObject,
    mut v_x_1256_: usize,
    mut v_x_1257_: usize,
    mut v_x_1258_: *mut crate::leanh::LeanObject,
    mut v_x_1259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: usize = 0;
    let mut v___x_1262_: usize = 0;
    let mut v___x_1263_: usize = 0;
    let mut v___x_1264_: usize = 0;
    let mut v_j_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1270_: u8 = 0;
    let mut v_v_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1284_: u8 = 0;
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut v_node_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1295_: u8 = 0;
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: usize = 0;
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1302_: u8 = 0;
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1304_: u8 = 0;
    let mut v_unused_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1310_: u8 = 0;
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1315_: u8 = 0;
    let mut v_ks_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: usize = 0;
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: u8 = 0;
    let mut v_reuseFailAlloc_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1255_) == 0 {
                    v_es_1260_ = crate::leanh::lean_ctor_get(v_x_1255_, 0);
                    v___x_1261_ = 5usize;
                    v___x_1262_ = 1usize;
                    v___x_1263_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
                    v___x_1264_ = lean_usize_land(v_x_1256_, v___x_1263_);
                    v_j_1265_ = lean_usize_to_nat(v___x_1264_);
                    v___x_1266_ = lean_array_get_size(v_es_1260_);
                    v___x_1267_ = lean_nat_dec_lt(v_j_1265_, v___x_1266_);
                    if v___x_1267_ == 0 {
                        crate::leanh::lean_dec(v_j_1265_);
                        crate::leanh::lean_dec(v_x_1259_);
                        crate::leanh::lean_dec_ref(v_x_1258_);
                        return v_x_1255_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1260_);
                        v_isSharedCheck_1304_ = (!crate::leanh::lean_is_exclusive(v_x_1255_)) as u8;
                        if v_isSharedCheck_1304_ == 0 {
                            v_unused_1305_ = crate::leanh::lean_ctor_get(v_x_1255_, 0);
                            crate::leanh::lean_dec(v_unused_1305_);
                            v___x_1269_ = v_x_1255_;
                            v_isShared_1270_ = v_isSharedCheck_1304_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1255_);
                            v___x_1269_ = crate::leanh::lean_box(0);
                            v_isShared_1270_ = v_isSharedCheck_1304_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1306_ = crate::leanh::lean_ctor_get(v_x_1255_, 0);
                    v_vs_1307_ = crate::leanh::lean_ctor_get(v_x_1255_, 1);
                    v_isSharedCheck_1327_ = (!crate::leanh::lean_is_exclusive(v_x_1255_)) as u8;
                    if v_isSharedCheck_1327_ == 0 {
                        v___x_1309_ = v_x_1255_;
                        v_isShared_1310_ = v_isSharedCheck_1327_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1307_);
                        crate::leanh::lean_inc(v_ks_1306_);
                        crate::leanh::lean_dec(v_x_1255_);
                        v___x_1309_ = crate::leanh::lean_box(0);
                        v_isShared_1310_ = v_isSharedCheck_1327_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1271_ = lean_array_fget(v_es_1260_, v_j_1265_);
                v___x_1272_ = crate::leanh::lean_box(0);
                v_xs_x27_1273_ = lean_array_fset(v_es_1260_, v_j_1265_, v___x_1272_);
                match crate::leanh::lean_obj_tag(v_v_1271_) {
                    0 => {
                        v_key_1280_ = crate::leanh::lean_ctor_get(v_v_1271_, 0);
                        v_val_1281_ = crate::leanh::lean_ctor_get(v_v_1271_, 1);
                        v_isSharedCheck_1291_ = (!crate::leanh::lean_is_exclusive(v_v_1271_)) as u8;
                        if v_isSharedCheck_1291_ == 0 {
                            v___x_1283_ = v_v_1271_;
                            v_isShared_1284_ = v_isSharedCheck_1291_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1281_);
                            crate::leanh::lean_inc(v_key_1280_);
                            crate::leanh::lean_dec(v_v_1271_);
                            v___x_1283_ = crate::leanh::lean_box(0);
                            v_isShared_1284_ = v_isSharedCheck_1291_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1292_ = crate::leanh::lean_ctor_get(v_v_1271_, 0);
                        v_isSharedCheck_1302_ = (!crate::leanh::lean_is_exclusive(v_v_1271_)) as u8;
                        if v_isSharedCheck_1302_ == 0 {
                            v___x_1294_ = v_v_1271_;
                            v_isShared_1295_ = v_isSharedCheck_1302_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1292_);
                            crate::leanh::lean_dec(v_v_1271_);
                            v___x_1294_ = crate::leanh::lean_box(0);
                            v_isShared_1295_ = v_isSharedCheck_1302_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1303_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1303_, 0, v_x_1258_);
                        crate::leanh::lean_ctor_set(v___x_1303_, 1, v_x_1259_);
                        v___y_1275_ = v___x_1303_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1276_ = lean_array_fset(v_xs_x27_1273_, v_j_1265_, v___y_1275_);
                crate::leanh::lean_dec(v_j_1265_);
                if v_isShared_1270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1269_, 0, v___x_1276_);
                    v___x_1278_ = v___x_1269_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1279_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
                    v___x_1278_ = v_reuseFailAlloc_1279_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1278_;
            }
            4 => {
                v___x_1285_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_1258_,
                        v_key_1280_,
                    );
                if v___x_1285_ == 0 {
                    crate::leanh::lean_del_object(v___x_1283_);
                    v___x_1286_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1280_,
                        v_val_1281_,
                        v_x_1258_,
                        v_x_1259_,
                    );
                    v___x_1287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1287_, 0, v___x_1286_);
                    v___y_1275_ = v___x_1287_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1281_);
                    crate::leanh::lean_dec(v_key_1280_);
                    if v_isShared_1284_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1283_, 1, v_x_1259_);
                        crate::leanh::lean_ctor_set(v___x_1283_, 0, v_x_1258_);
                        v___x_1289_ = v___x_1283_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1290_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_x_1258_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_x_1259_);
                        v___x_1289_ = v_reuseFailAlloc_1290_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1275_ = v___x_1289_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1296_ = lean_usize_shift_right(v_x_1256_, v___x_1261_);
                v___x_1297_ = lean_usize_add(v_x_1257_, v___x_1262_);
                v___x_1298_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_node_1292_, v___x_1296_, v___x_1297_, v_x_1258_, v_x_1259_);
                if v_isShared_1295_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1294_, 0, v___x_1298_);
                    v___x_1300_ = v___x_1294_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
                    v___x_1300_ = v_reuseFailAlloc_1301_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1275_ = v___x_1300_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1310_ == 0 {
                    v___x_1312_ = v___x_1309_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1326_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_ks_1306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_vs_1307_);
                    v___x_1312_ = v_reuseFailAlloc_1326_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1313_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v___x_1312_, v_x_1258_, v_x_1259_);
                v___x_1321_ = 7usize;
                v___x_1322_ = lean_usize_dec_le(v___x_1321_, v_x_1257_);
                if v___x_1322_ == 0 {
                    v___x_1323_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1313_);
                    v___x_1324_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1325_ = lean_nat_dec_lt(v___x_1323_, v___x_1324_);
                    crate::leanh::lean_dec(v___x_1323_);
                    v___y_1315_ = v___x_1325_;
                    state = 10;
                    continue;
                } else {
                    v___y_1315_ = v___x_1322_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1315_ == 0 {
                    v_ks_1316_ = crate::leanh::lean_ctor_get(v_newNode_1313_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1316_);
                    v_vs_1317_ = crate::leanh::lean_ctor_get(v_newNode_1313_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1317_);
                    crate::leanh::lean_dec_ref(v_newNode_1313_);
                    v___x_1318_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1319_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0);
                    v___x_1320_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_x_1257_, v_ks_1316_, v_vs_1317_, v___x_1318_, v___x_1319_);
                    crate::leanh::lean_dec_ref(v_vs_1317_);
                    crate::leanh::lean_dec_ref(v_ks_1316_);
                    return v___x_1320_;
                } else {
                    return v_newNode_1313_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(
    mut v_depth_1328_: usize,
    mut v_keys_1329_: *mut crate::leanh::LeanObject,
    mut v_vals_1330_: *mut crate::leanh::LeanObject,
    mut v_i_1331_: *mut crate::leanh::LeanObject,
    mut v_entries_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: u8 = 0;
    let mut v_k_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u64 = 0;
    let mut v_h_1338_: usize = 0;
    let mut v___x_1339_: usize = 0;
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: usize = 0;
    let mut v___x_1342_: usize = 0;
    let mut v___x_1343_: usize = 0;
    let mut v_h_1344_: usize = 0;
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1333_ = lean_array_get_size(v_keys_1329_);
                v___x_1334_ = lean_nat_dec_lt(v_i_1331_, v___x_1333_);
                if v___x_1334_ == 0 {
                    crate::leanh::lean_dec(v_i_1331_);
                    return v_entries_1332_;
                } else {
                    v_k_1335_ = lean_array_fget_borrowed(v_keys_1329_, v_i_1331_);
                    v_v_1336_ = lean_array_fget_borrowed(v_vals_1330_, v_i_1331_);
                    v___x_1337_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1335_);
                    v_h_1338_ = lean_uint64_to_usize(v___x_1337_);
                    v___x_1339_ = 5usize;
                    v___x_1340_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1341_ = 1usize;
                    v___x_1342_ = lean_usize_sub(v_depth_1328_, v___x_1341_);
                    v___x_1343_ = lean_usize_mul(v___x_1339_, v___x_1342_);
                    v_h_1344_ = lean_usize_shift_right(v_h_1338_, v___x_1343_);
                    v___x_1345_ = lean_nat_add(v_i_1331_, v___x_1340_);
                    crate::leanh::lean_dec(v_i_1331_);
                    crate::leanh::lean_inc(v_v_1336_);
                    crate::leanh::lean_inc(v_k_1335_);
                    v___x_1346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_entries_1332_, v_h_1344_, v_depth_1328_, v_k_1335_, v_v_1336_);
                    v_i_1331_ = v___x_1345_;
                    v_entries_1332_ = v___x_1346_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg___boxed(
    mut v_depth_1348_: *mut crate::leanh::LeanObject,
    mut v_keys_1349_: *mut crate::leanh::LeanObject,
    mut v_vals_1350_: *mut crate::leanh::LeanObject,
    mut v_i_1351_: *mut crate::leanh::LeanObject,
    mut v_entries_1352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1353_: usize = 0;
    let mut v_res_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1353_ = crate::leanh::lean_unbox_usize(v_depth_1348_);
    crate::leanh::lean_dec(v_depth_1348_);
    v_res_1354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_boxed_1353_, v_keys_1349_, v_vals_1350_, v_i_1351_, v_entries_1352_);
    crate::leanh::lean_dec_ref(v_vals_1350_);
    crate::leanh::lean_dec_ref(v_keys_1349_);
    return v_res_1354_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___boxed(
    mut v_x_1355_: *mut crate::leanh::LeanObject,
    mut v_x_1356_: *mut crate::leanh::LeanObject,
    mut v_x_1357_: *mut crate::leanh::LeanObject,
    mut v_x_1358_: *mut crate::leanh::LeanObject,
    mut v_x_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9652__boxed_1360_: usize = 0;
    let mut v_x_9653__boxed_1361_: usize = 0;
    let mut v_res_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9652__boxed_1360_ = crate::leanh::lean_unbox_usize(v_x_1356_);
    crate::leanh::lean_dec(v_x_1356_);
    v_x_9653__boxed_1361_ = crate::leanh::lean_unbox_usize(v_x_1357_);
    crate::leanh::lean_dec(v_x_1357_);
    v_res_1362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_1355_, v_x_9652__boxed_1360_, v_x_9653__boxed_1361_, v_x_1358_, v_x_1359_);
    return v_res_1362_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(
    mut v_x_1363_: *mut crate::leanh::LeanObject,
    mut v_x_1364_: *mut crate::leanh::LeanObject,
    mut v_x_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1366_: u64 = 0;
    let mut v___x_1367_: usize = 0;
    let mut v___x_1368_: usize = 0;
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1364_);
    v___x_1367_ = lean_uint64_to_usize(v___x_1366_);
    v___x_1368_ = 1usize;
    v___x_1369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_1363_, v___x_1367_, v___x_1368_, v_x_1364_, v_x_1365_);
    return v___x_1369_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1373_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2;
    v___x_1374_ = crate::leanh::lean_unsigned_to_nat(26);
    v___x_1375_ = crate::leanh::lean_unsigned_to_nat(19);
    v___x_1376_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1;
    v___x_1377_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0;
    v___x_1378_ = l_mkPanicMessageWithDecl(
        v___x_1377_,
        v___x_1376_,
        v___x_1375_,
        v___x_1374_,
        v___x_1373_,
    );
    return v___x_1378_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = crate::leanh::lean_box(0);
    v_dummy_1392_ = l_Lean_Expr_sort___override(v___x_1391_);
    return v_dummy_1392_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(
    mut v_f_1398_: *mut crate::leanh::LeanObject,
    mut v_a_1399_: *mut crate::leanh::LeanObject,
    mut v_a_1400_: *mut crate::leanh::LeanObject,
    mut v_a_1401_: *mut crate::leanh::LeanObject,
    mut v_a_1402_: *mut crate::leanh::LeanObject,
    mut v_a_1403_: *mut crate::leanh::LeanObject,
    mut v_a_1404_: *mut crate::leanh::LeanObject,
    mut v_a_1405_: *mut crate::leanh::LeanObject,
    mut v_a_1406_: *mut crate::leanh::LeanObject,
    mut v_a_1407_: *mut crate::leanh::LeanObject,
    mut v_a_1408_: *mut crate::leanh::LeanObject,
    mut v_a_1409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fns_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v_inv_x3f_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1443_: u8 = 0;
    let mut v_00_u03b1_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b2_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v_head_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1471_: u8 = 0;
    let mut v_nextDeclIdx_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newFacts_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_1480_: u8 = 0;
    let mut v_nextIdx_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sstates_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1491_: u8 = 0;
    let mut v_thms_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fns_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v_dummy_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut v_isSharedCheck_1529_: u8 = 0;
    let mut v_unused_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_unused_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_a_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1537_: u8 = 0;
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v_reuseFailAlloc_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut v_unused_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v_unused_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1548_: u8 = 0;
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1551_: u8 = 0;
    let mut v_unused_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1424_ = lean_st_ref_get(v_a_1400_);
                v_toGoalState_1425_ = crate::leanh::lean_ctor_get(v___x_1424_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_1425_);
                crate::leanh::lean_dec(v___x_1424_);
                v_inj_1426_ = crate::leanh::lean_ctor_get(v_toGoalState_1425_, 13);
                crate::leanh::lean_inc_ref(v_inj_1426_);
                crate::leanh::lean_dec_ref(v_toGoalState_1425_);
                v_fns_1427_ = crate::leanh::lean_ctor_get(v_inj_1426_, 1);
                v_isSharedCheck_1551_ = (!crate::leanh::lean_is_exclusive(v_inj_1426_)) as u8;
                if v_isSharedCheck_1551_ == 0 {
                    v_unused_1552_ = crate::leanh::lean_ctor_get(v_inj_1426_, 0);
                    crate::leanh::lean_dec(v_unused_1552_);
                    v___x_1429_ = v_inj_1426_;
                    v_isShared_1430_ = v_isSharedCheck_1551_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fns_1427_);
                    crate::leanh::lean_dec(v_inj_1426_);
                    v___x_1429_ = crate::leanh::lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1551_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1422_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3);
                v___x_1423_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v___x_1422_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
                return v___x_1423_;
            }
            2 => {
                v___x_1431_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_fns_1427_, v_f_1398_);
                crate::leanh::lean_dec_ref(v_fns_1427_);
                if crate::leanh::lean_obj_tag(v___x_1431_) == 1 {
                    v_val_1432_ = crate::leanh::lean_ctor_get(v___x_1431_, 0);
                    v_isSharedCheck_1548_ = (!crate::leanh::lean_is_exclusive(v___x_1431_)) as u8;
                    if v_isSharedCheck_1548_ == 0 {
                        v___x_1434_ = v___x_1431_;
                        v_isShared_1435_ = v_isSharedCheck_1548_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1432_);
                        crate::leanh::lean_dec(v___x_1431_);
                        v___x_1434_ = crate::leanh::lean_box(0);
                        v_isShared_1435_ = v_isSharedCheck_1548_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1431_);
                    crate::leanh::lean_del_object(v___x_1429_);
                    crate::leanh::lean_dec_ref(v_a_1399_);
                    crate::leanh::lean_dec_ref(v_f_1398_);
                    v___x_1549_ = crate::leanh::lean_box(0);
                    v___x_1550_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1550_, 0, v___x_1549_);
                    return v___x_1550_;
                }
            }
            3 => {
                v_inv_x3f_1436_ = crate::leanh::lean_ctor_get(v_val_1432_, 4);
                if crate::leanh::lean_obj_tag(v_inv_x3f_1436_) == 1 {
                    crate::leanh::lean_inc_ref(v_inv_x3f_1436_);
                    crate::leanh::lean_del_object(v___x_1434_);
                    crate::leanh::lean_dec(v_val_1432_);
                    crate::leanh::lean_del_object(v___x_1429_);
                    crate::leanh::lean_dec_ref(v_a_1399_);
                    crate::leanh::lean_dec_ref(v_f_1398_);
                    v___x_1437_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1437_, 0, v_inv_x3f_1436_);
                    return v___x_1437_;
                } else {
                    v_us_1438_ = crate::leanh::lean_ctor_get(v_val_1432_, 0);
                    crate::leanh::lean_inc(v_us_1438_);
                    if crate::leanh::lean_obj_tag(v_us_1438_) == 1 {
                        v_tail_1439_ = crate::leanh::lean_ctor_get(v_us_1438_, 1);
                        crate::leanh::lean_inc(v_tail_1439_);
                        if crate::leanh::lean_obj_tag(v_tail_1439_) == 1 {
                            v_tail_1440_ = crate::leanh::lean_ctor_get(v_tail_1439_, 1);
                            v_isSharedCheck_1546_ =
                                (!crate::leanh::lean_is_exclusive(v_tail_1439_)) as u8;
                            if v_isSharedCheck_1546_ == 0 {
                                v_unused_1547_ = crate::leanh::lean_ctor_get(v_tail_1439_, 0);
                                crate::leanh::lean_dec(v_unused_1547_);
                                v___x_1442_ = v_tail_1439_;
                                v_isShared_1443_ = v_isSharedCheck_1546_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_tail_1440_);
                                crate::leanh::lean_dec(v_tail_1439_);
                                v___x_1442_ = crate::leanh::lean_box(0);
                                v_isShared_1443_ = v_isSharedCheck_1546_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_tail_1439_);
                            crate::leanh::lean_dec_ref_known(v_us_1438_, 2);
                            crate::leanh::lean_del_object(v___x_1434_);
                            crate::leanh::lean_dec(v_val_1432_);
                            crate::leanh::lean_del_object(v___x_1429_);
                            crate::leanh::lean_dec_ref(v_a_1399_);
                            crate::leanh::lean_dec_ref(v_f_1398_);
                            v___y_1412_ = v_a_1400_;
                            v___y_1413_ = v_a_1401_;
                            v___y_1414_ = v_a_1402_;
                            v___y_1415_ = v_a_1403_;
                            v___y_1416_ = v_a_1404_;
                            v___y_1417_ = v_a_1405_;
                            v___y_1418_ = v_a_1406_;
                            v___y_1419_ = v_a_1407_;
                            v___y_1420_ = v_a_1408_;
                            v___y_1421_ = v_a_1409_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_us_1438_);
                        crate::leanh::lean_del_object(v___x_1434_);
                        crate::leanh::lean_dec(v_val_1432_);
                        crate::leanh::lean_del_object(v___x_1429_);
                        crate::leanh::lean_dec_ref(v_a_1399_);
                        crate::leanh::lean_dec_ref(v_f_1398_);
                        v___y_1412_ = v_a_1400_;
                        v___y_1413_ = v_a_1401_;
                        v___y_1414_ = v_a_1402_;
                        v___y_1415_ = v_a_1403_;
                        v___y_1416_ = v_a_1404_;
                        v___y_1417_ = v_a_1405_;
                        v___y_1418_ = v_a_1406_;
                        v___y_1419_ = v_a_1407_;
                        v___y_1420_ = v_a_1408_;
                        v___y_1421_ = v_a_1409_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_tail_1440_) == 0 {
                    v_00_u03b1_1444_ = crate::leanh::lean_ctor_get(v_val_1432_, 1);
                    v_00_u03b2_1445_ = crate::leanh::lean_ctor_get(v_val_1432_, 2);
                    v_h_1446_ = crate::leanh::lean_ctor_get(v_val_1432_, 3);
                    v_isSharedCheck_1543_ = (!crate::leanh::lean_is_exclusive(v_val_1432_)) as u8;
                    if v_isSharedCheck_1543_ == 0 {
                        v_unused_1544_ = crate::leanh::lean_ctor_get(v_val_1432_, 4);
                        crate::leanh::lean_dec(v_unused_1544_);
                        v_unused_1545_ = crate::leanh::lean_ctor_get(v_val_1432_, 0);
                        crate::leanh::lean_dec(v_unused_1545_);
                        v___x_1448_ = v_val_1432_;
                        v_isShared_1449_ = v_isSharedCheck_1543_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_h_1446_);
                        crate::leanh::lean_inc(v_00_u03b2_1445_);
                        crate::leanh::lean_inc(v_00_u03b1_1444_);
                        crate::leanh::lean_dec(v_val_1432_);
                        v___x_1448_ = crate::leanh::lean_box(0);
                        v_isShared_1449_ = v_isSharedCheck_1543_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1442_);
                    crate::leanh::lean_dec(v_tail_1440_);
                    crate::leanh::lean_dec_ref_known(v_us_1438_, 2);
                    crate::leanh::lean_del_object(v___x_1434_);
                    crate::leanh::lean_dec(v_val_1432_);
                    crate::leanh::lean_del_object(v___x_1429_);
                    crate::leanh::lean_dec_ref(v_a_1399_);
                    crate::leanh::lean_dec_ref(v_f_1398_);
                    v___y_1412_ = v_a_1400_;
                    v___y_1413_ = v_a_1401_;
                    v___y_1414_ = v_a_1402_;
                    v___y_1415_ = v_a_1403_;
                    v___y_1416_ = v_a_1404_;
                    v___y_1417_ = v_a_1405_;
                    v___y_1418_ = v_a_1406_;
                    v___y_1419_ = v_a_1407_;
                    v___y_1420_ = v_a_1408_;
                    v___y_1421_ = v_a_1409_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v_head_1450_ = crate::leanh::lean_ctor_get(v_us_1438_, 0);
                v___x_1451_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6;
                crate::leanh::lean_inc(v_head_1450_);
                if v_isShared_1443_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1442_, 0, v_head_1450_);
                    v___x_1453_ = v___x_1442_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_head_1450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_tail_1440_);
                    v___x_1453_ = v_reuseFailAlloc_1542_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1454_ = l_Lean_mkConst(v___x_1451_, v___x_1453_);
                crate::leanh::lean_inc_ref_n(v_00_u03b1_1444_, 2);
                v___x_1455_ = l_Lean_mkAppB(v___x_1454_, v_00_u03b1_1444_, v_a_1399_);
                v___x_1456_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10;
                crate::leanh::lean_inc_ref(v_us_1438_);
                v___x_1457_ = l_Lean_mkConst(v___x_1456_, v_us_1438_);
                crate::leanh::lean_inc_ref(v_h_1446_);
                crate::leanh::lean_inc_ref(v_f_1398_);
                crate::leanh::lean_inc_ref(v_00_u03b2_1445_);
                v___x_1458_ = l_Lean_mkApp5(
                    v___x_1457_,
                    v_00_u03b1_1444_,
                    v_00_u03b2_1445_,
                    v_f_1398_,
                    v_h_1446_,
                    v___x_1455_,
                );
                v___x_1459_ = l_Lean_Meta_Grind_preprocessLight___redArg(
                    v___x_1458_,
                    v_a_1401_,
                    v_a_1402_,
                    v_a_1403_,
                    v_a_1404_,
                    v_a_1405_,
                    v_a_1406_,
                    v_a_1407_,
                    v_a_1408_,
                    v_a_1409_,
                );
                if crate::leanh::lean_obj_tag(v___x_1459_) == 0 {
                    v_a_1460_ = crate::leanh::lean_ctor_get(v___x_1459_, 0);
                    v_isSharedCheck_1533_ = (!crate::leanh::lean_is_exclusive(v___x_1459_)) as u8;
                    if v_isSharedCheck_1533_ == 0 {
                        v___x_1462_ = v___x_1459_;
                        v_isShared_1463_ = v_isSharedCheck_1533_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1460_);
                        crate::leanh::lean_dec(v___x_1459_);
                        v___x_1462_ = crate::leanh::lean_box(0);
                        v_isShared_1463_ = v_isSharedCheck_1533_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1448_);
                    crate::leanh::lean_dec_ref(v_h_1446_);
                    crate::leanh::lean_dec_ref(v_00_u03b2_1445_);
                    crate::leanh::lean_dec_ref(v_00_u03b1_1444_);
                    crate::leanh::lean_dec_ref_known(v_us_1438_, 2);
                    crate::leanh::lean_del_object(v___x_1434_);
                    crate::leanh::lean_del_object(v___x_1429_);
                    crate::leanh::lean_dec_ref(v_f_1398_);
                    v_a_1534_ = crate::leanh::lean_ctor_get(v___x_1459_, 0);
                    v_isSharedCheck_1541_ = (!crate::leanh::lean_is_exclusive(v___x_1459_)) as u8;
                    if v_isSharedCheck_1541_ == 0 {
                        v___x_1536_ = v___x_1459_;
                        v_isShared_1537_ = v_isSharedCheck_1541_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1534_);
                        crate::leanh::lean_dec(v___x_1459_);
                        v___x_1536_ = crate::leanh::lean_box(0);
                        v_isShared_1537_ = v_isSharedCheck_1541_;
                        state = 18;
                        continue;
                    }
                }
            }
            7 => {
                v___x_1464_ = lean_st_ref_take(v_a_1400_);
                v_nargs_1465_ = l_Lean_Expr_getAppNumArgs(v_a_1460_);
                v_toGoalState_1466_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_1466_);
                v_inj_1467_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 13);
                crate::leanh::lean_inc_ref(v_inj_1467_);
                v_mvarId_1468_ = crate::leanh::lean_ctor_get(v___x_1464_, 1);
                v_isSharedCheck_1531_ = (!crate::leanh::lean_is_exclusive(v___x_1464_)) as u8;
                if v_isSharedCheck_1531_ == 0 {
                    v_unused_1532_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
                    crate::leanh::lean_dec(v_unused_1532_);
                    v___x_1470_ = v___x_1464_;
                    v_isShared_1471_ = v_isSharedCheck_1531_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_1468_);
                    crate::leanh::lean_dec(v___x_1464_);
                    v___x_1470_ = crate::leanh::lean_box(0);
                    v_isShared_1471_ = v_isSharedCheck_1531_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_nextDeclIdx_1472_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 0);
                v_enodeMap_1473_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 1);
                v_exprs_1474_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 2);
                v_parents_1475_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 3);
                v_congrTable_1476_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 4);
                v_appMap_1477_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 5);
                v_indicesFound_1478_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 6);
                v_newFacts_1479_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 7);
                v_inconsistent_1480_ = crate::leanh::lean_ctor_get_uint8(
                    v_toGoalState_1466_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_nextIdx_1481_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 8);
                v_newRawFacts_1482_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 9);
                v_facts_1483_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 10);
                v_extThms_1484_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 11);
                v_ematch_1485_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 12);
                v_split_1486_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 14);
                v_clean_1487_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 15);
                v_sstates_1488_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 16);
                v_isSharedCheck_1529_ =
                    (!crate::leanh::lean_is_exclusive(v_toGoalState_1466_)) as u8;
                if v_isSharedCheck_1529_ == 0 {
                    v_unused_1530_ = crate::leanh::lean_ctor_get(v_toGoalState_1466_, 13);
                    crate::leanh::lean_dec(v_unused_1530_);
                    v___x_1490_ = v_toGoalState_1466_;
                    v_isShared_1491_ = v_isSharedCheck_1529_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_sstates_1488_);
                    crate::leanh::lean_inc(v_clean_1487_);
                    crate::leanh::lean_inc(v_split_1486_);
                    crate::leanh::lean_inc(v_ematch_1485_);
                    crate::leanh::lean_inc(v_extThms_1484_);
                    crate::leanh::lean_inc(v_facts_1483_);
                    crate::leanh::lean_inc(v_newRawFacts_1482_);
                    crate::leanh::lean_inc(v_nextIdx_1481_);
                    crate::leanh::lean_inc(v_newFacts_1479_);
                    crate::leanh::lean_inc(v_indicesFound_1478_);
                    crate::leanh::lean_inc(v_appMap_1477_);
                    crate::leanh::lean_inc(v_congrTable_1476_);
                    crate::leanh::lean_inc(v_parents_1475_);
                    crate::leanh::lean_inc(v_exprs_1474_);
                    crate::leanh::lean_inc(v_enodeMap_1473_);
                    crate::leanh::lean_inc(v_nextDeclIdx_1472_);
                    crate::leanh::lean_dec(v_toGoalState_1466_);
                    v___x_1490_ = crate::leanh::lean_box(0);
                    v_isShared_1491_ = v_isSharedCheck_1529_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_thms_1492_ = crate::leanh::lean_ctor_get(v_inj_1467_, 0);
                v_fns_1493_ = crate::leanh::lean_ctor_get(v_inj_1467_, 1);
                v_isSharedCheck_1528_ = (!crate::leanh::lean_is_exclusive(v_inj_1467_)) as u8;
                if v_isSharedCheck_1528_ == 0 {
                    v___x_1495_ = v_inj_1467_;
                    v_isShared_1496_ = v_isSharedCheck_1528_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fns_1493_);
                    crate::leanh::lean_inc(v_thms_1492_);
                    crate::leanh::lean_dec(v_inj_1467_);
                    v___x_1495_ = crate::leanh::lean_box(0);
                    v_isShared_1496_ = v_isSharedCheck_1528_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_dummy_1497_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11);
                crate::leanh::lean_inc(v_nargs_1465_);
                v___x_1498_ = lean_mk_array(v_nargs_1465_, v_dummy_1497_);
                v___x_1499_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1500_ = lean_nat_sub(v_nargs_1465_, v___x_1499_);
                crate::leanh::lean_dec(v_nargs_1465_);
                crate::leanh::lean_inc(v_a_1460_);
                v___x_1501_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_a_1460_,
                    v___x_1498_,
                    v___x_1500_,
                );
                v___x_1502_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13;
                crate::leanh::lean_inc_ref(v_us_1438_);
                v___x_1503_ = l_Lean_mkConst(v___x_1502_, v_us_1438_);
                v___x_1504_ = l_Lean_mkAppN(v___x_1503_, v___x_1501_);
                crate::leanh::lean_dec_ref(v___x_1501_);
                if v_isShared_1430_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1429_, 1, v___x_1504_);
                    crate::leanh::lean_ctor_set(v___x_1429_, 0, v_a_1460_);
                    v___x_1506_ = v___x_1429_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1504_);
                    v___x_1506_ = v_reuseFailAlloc_1527_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1435_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1434_, 0, v___x_1506_);
                    v___x_1508_ = v___x_1434_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1506_);
                    v___x_1508_ = v_reuseFailAlloc_1526_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_inc_ref(v___x_1508_);
                if v_isShared_1449_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1448_, 4, v___x_1508_);
                    v___x_1510_ = v___x_1448_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1525_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_us_1438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_00_u03b1_1444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_00_u03b2_1445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_h_1446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1525_, 4, v___x_1508_);
                    v___x_1510_ = v_reuseFailAlloc_1525_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1511_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_1493_, v_f_1398_, v___x_1510_);
                if v_isShared_1496_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1495_, 1, v___x_1511_);
                    v___x_1513_ = v___x_1495_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_thms_1492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1511_);
                    v___x_1513_ = v_reuseFailAlloc_1524_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1491_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1490_, 13, v___x_1513_);
                    v___x_1515_ = v___x_1490_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1523_ = crate::leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_nextDeclIdx_1472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_enodeMap_1473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_exprs_1474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_parents_1475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_congrTable_1476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 5, v_appMap_1477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 6, v_indicesFound_1478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 7, v_newFacts_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 8, v_nextIdx_1481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 9, v_newRawFacts_1482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 10, v_facts_1483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 11, v_extThms_1484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 12, v_ematch_1485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 13, v___x_1513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 14, v_split_1486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 15, v_clean_1487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 16, v_sstates_1488_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1523_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_inconsistent_1480_,
                    );
                    v___x_1515_ = v_reuseFailAlloc_1523_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1471_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1470_, 0, v___x_1515_);
                    v___x_1517_ = v___x_1470_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1522_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_mvarId_1468_);
                    v___x_1517_ = v_reuseFailAlloc_1522_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_1518_ = lean_st_ref_set(v_a_1400_, v___x_1517_);
                if v_isShared_1463_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1462_, 0, v___x_1508_);
                    v___x_1520_ = v___x_1462_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1521_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1508_);
                    v___x_1520_ = v_reuseFailAlloc_1521_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1520_;
            }
            18 => {
                if v_isShared_1537_ == 0 {
                    v___x_1539_ = v___x_1536_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
                    v___x_1539_ = v_reuseFailAlloc_1540_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___boxed(
    mut v_f_1553_: *mut crate::leanh::LeanObject,
    mut v_a_1554_: *mut crate::leanh::LeanObject,
    mut v_a_1555_: *mut crate::leanh::LeanObject,
    mut v_a_1556_: *mut crate::leanh::LeanObject,
    mut v_a_1557_: *mut crate::leanh::LeanObject,
    mut v_a_1558_: *mut crate::leanh::LeanObject,
    mut v_a_1559_: *mut crate::leanh::LeanObject,
    mut v_a_1560_: *mut crate::leanh::LeanObject,
    mut v_a_1561_: *mut crate::leanh::LeanObject,
    mut v_a_1562_: *mut crate::leanh::LeanObject,
    mut v_a_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1566_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(
        v_f_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_,
        v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_,
    );
    crate::leanh::lean_dec(v_a_1564_);
    crate::leanh::lean_dec_ref(v_a_1563_);
    crate::leanh::lean_dec(v_a_1562_);
    crate::leanh::lean_dec_ref(v_a_1561_);
    crate::leanh::lean_dec(v_a_1560_);
    crate::leanh::lean_dec_ref(v_a_1559_);
    crate::leanh::lean_dec(v_a_1558_);
    crate::leanh::lean_dec_ref(v_a_1557_);
    crate::leanh::lean_dec(v_a_1556_);
    crate::leanh::lean_dec(v_a_1555_);
    return v_res_1566_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(
    mut v_00_u03b2_1567_: *mut crate::leanh::LeanObject,
    mut v_x_1568_: *mut crate::leanh::LeanObject,
    mut v_x_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1570_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_1568_, v_x_1569_);
    return v___x_1570_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___boxed(
    mut v_00_u03b2_1571_: *mut crate::leanh::LeanObject,
    mut v_x_1572_: *mut crate::leanh::LeanObject,
    mut v_x_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(v_00_u03b2_1571_, v_x_1572_, v_x_1573_);
    crate::leanh::lean_dec_ref(v_x_1573_);
    crate::leanh::lean_dec_ref(v_x_1572_);
    return v_res_1574_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2(
    mut v_00_u03b2_1575_: *mut crate::leanh::LeanObject,
    mut v_x_1576_: *mut crate::leanh::LeanObject,
    mut v_x_1577_: *mut crate::leanh::LeanObject,
    mut v_x_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1579_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_x_1576_, v_x_1577_, v_x_1578_);
    return v___x_1579_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(
    mut v_00_u03b2_1580_: *mut crate::leanh::LeanObject,
    mut v_x_1581_: *mut crate::leanh::LeanObject,
    mut v_x_1582_: usize,
    mut v_x_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_1581_, v_x_1582_, v_x_1583_);
    return v___x_1584_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___boxed(
    mut v_00_u03b2_1585_: *mut crate::leanh::LeanObject,
    mut v_x_1586_: *mut crate::leanh::LeanObject,
    mut v_x_1587_: *mut crate::leanh::LeanObject,
    mut v_x_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_10143__boxed_1589_: usize = 0;
    let mut v_res_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_10143__boxed_1589_ = crate::leanh::lean_unbox_usize(v_x_1587_);
    crate::leanh::lean_dec(v_x_1587_);
    v_res_1590_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(v_00_u03b2_1585_, v_x_1586_, v_x_10143__boxed_1589_, v_x_1588_);
    crate::leanh::lean_dec_ref(v_x_1588_);
    crate::leanh::lean_dec_ref(v_x_1586_);
    return v_res_1590_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(
    mut v_00_u03b2_1591_: *mut crate::leanh::LeanObject,
    mut v_x_1592_: *mut crate::leanh::LeanObject,
    mut v_x_1593_: usize,
    mut v_x_1594_: usize,
    mut v_x_1595_: *mut crate::leanh::LeanObject,
    mut v_x_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_1592_, v_x_1593_, v_x_1594_, v_x_1595_, v_x_1596_);
    return v___x_1597_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___boxed(
    mut v_00_u03b2_1598_: *mut crate::leanh::LeanObject,
    mut v_x_1599_: *mut crate::leanh::LeanObject,
    mut v_x_1600_: *mut crate::leanh::LeanObject,
    mut v_x_1601_: *mut crate::leanh::LeanObject,
    mut v_x_1602_: *mut crate::leanh::LeanObject,
    mut v_x_1603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_10154__boxed_1604_: usize = 0;
    let mut v_x_10155__boxed_1605_: usize = 0;
    let mut v_res_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_10154__boxed_1604_ = crate::leanh::lean_unbox_usize(v_x_1600_);
    crate::leanh::lean_dec(v_x_1600_);
    v_x_10155__boxed_1605_ = crate::leanh::lean_unbox_usize(v_x_1601_);
    crate::leanh::lean_dec(v_x_1601_);
    v_res_1606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(v_00_u03b2_1598_, v_x_1599_, v_x_10154__boxed_1604_, v_x_10155__boxed_1605_, v_x_1602_, v_x_1603_);
    return v_res_1606_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(
    mut v_00_u03b2_1607_: *mut crate::leanh::LeanObject,
    mut v_keys_1608_: *mut crate::leanh::LeanObject,
    mut v_vals_1609_: *mut crate::leanh::LeanObject,
    mut v_heq_1610_: *mut crate::leanh::LeanObject,
    mut v_i_1611_: *mut crate::leanh::LeanObject,
    mut v_k_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1613_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_1608_, v_vals_1609_, v_i_1611_, v_k_1612_);
    return v___x_1613_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_1614_: *mut crate::leanh::LeanObject,
    mut v_keys_1615_: *mut crate::leanh::LeanObject,
    mut v_vals_1616_: *mut crate::leanh::LeanObject,
    mut v_heq_1617_: *mut crate::leanh::LeanObject,
    mut v_i_1618_: *mut crate::leanh::LeanObject,
    mut v_k_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(v_00_u03b2_1614_, v_keys_1615_, v_vals_1616_, v_heq_1617_, v_i_1618_, v_k_1619_);
    crate::leanh::lean_dec_ref(v_k_1619_);
    crate::leanh::lean_dec_ref(v_vals_1616_);
    crate::leanh::lean_dec_ref(v_keys_1615_);
    return v_res_1620_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5(
    mut v_00_u03b2_1621_: *mut crate::leanh::LeanObject,
    mut v_n_1622_: *mut crate::leanh::LeanObject,
    mut v_k_1623_: *mut crate::leanh::LeanObject,
    mut v_v_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v_n_1622_, v_k_1623_, v_v_1624_);
    return v___x_1625_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(
    mut v_00_u03b2_1626_: *mut crate::leanh::LeanObject,
    mut v_depth_1627_: usize,
    mut v_keys_1628_: *mut crate::leanh::LeanObject,
    mut v_vals_1629_: *mut crate::leanh::LeanObject,
    mut v_heq_1630_: *mut crate::leanh::LeanObject,
    mut v_i_1631_: *mut crate::leanh::LeanObject,
    mut v_entries_1632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1633_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_1627_, v_keys_1628_, v_vals_1629_, v_i_1631_, v_entries_1632_);
    return v___x_1633_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b2_1634_: *mut crate::leanh::LeanObject,
    mut v_depth_1635_: *mut crate::leanh::LeanObject,
    mut v_keys_1636_: *mut crate::leanh::LeanObject,
    mut v_vals_1637_: *mut crate::leanh::LeanObject,
    mut v_heq_1638_: *mut crate::leanh::LeanObject,
    mut v_i_1639_: *mut crate::leanh::LeanObject,
    mut v_entries_1640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1641_: usize = 0;
    let mut v_res_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1641_ = crate::leanh::lean_unbox_usize(v_depth_1635_);
    crate::leanh::lean_dec(v_depth_1635_);
    v_res_1642_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(v_00_u03b2_1634_, v_depth_boxed_1641_, v_keys_1636_, v_vals_1637_, v_heq_1638_, v_i_1639_, v_entries_1640_);
    crate::leanh::lean_dec_ref(v_vals_1637_);
    crate::leanh::lean_dec_ref(v_keys_1636_);
    return v_res_1642_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6(
    mut v_00_u03b2_1643_: *mut crate::leanh::LeanObject,
    mut v_x_1644_: *mut crate::leanh::LeanObject,
    mut v_x_1645_: *mut crate::leanh::LeanObject,
    mut v_x_1646_: *mut crate::leanh::LeanObject,
    mut v_x_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1648_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_x_1644_, v_x_1645_, v_x_1646_, v_x_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(
    mut v_msgData_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
    mut v___y_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = lean_st_ref_get(v___y_1653_);
    v_env_1656_ = crate::leanh::lean_ctor_get(v___x_1655_, 0);
    crate::leanh::lean_inc_ref(v_env_1656_);
    crate::leanh::lean_dec(v___x_1655_);
    v___x_1657_ = lean_st_ref_get(v___y_1651_);
    v_mctx_1658_ = crate::leanh::lean_ctor_get(v___x_1657_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1658_);
    crate::leanh::lean_dec(v___x_1657_);
    v_lctx_1659_ = crate::leanh::lean_ctor_get(v___y_1650_, 2);
    v_options_1660_ = crate::leanh::lean_ctor_get(v___y_1652_, 2);
    crate::leanh::lean_inc_ref(v_options_1660_);
    crate::leanh::lean_inc_ref(v_lctx_1659_);
    v___x_1661_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1661_, 0, v_env_1656_);
    crate::leanh::lean_ctor_set(v___x_1661_, 1, v_mctx_1658_);
    crate::leanh::lean_ctor_set(v___x_1661_, 2, v_lctx_1659_);
    crate::leanh::lean_ctor_set(v___x_1661_, 3, v_options_1660_);
    v___x_1662_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1662_, 0, v___x_1661_);
    crate::leanh::lean_ctor_set(v___x_1662_, 1, v_msgData_1649_);
    v___x_1663_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1663_, 0, v___x_1662_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0___boxed(
    mut v_msgData_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
    mut v___y_1666_: *mut crate::leanh::LeanObject,
    mut v___y_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1670_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msgData_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
    crate::leanh::lean_dec(v___y_1668_);
    crate::leanh::lean_dec_ref(v___y_1667_);
    crate::leanh::lean_dec(v___y_1666_);
    crate::leanh::lean_dec_ref(v___y_1665_);
    return v_res_1670_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: f64 = 0.0;
    v___x_1671_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1672_ = lean_float_of_nat(v___x_1671_);
    return v___x_1672_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(
    mut v_cls_1676_: *mut crate::leanh::LeanObject,
    mut v_msg_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1688_: u8 = 0;
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v_tid_1702_: u64 = 0;
    let mut v_traces_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: f64 = 0.0;
    let mut v___x_1709_: u8 = 0;
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_isSharedCheck_1728_: u8 = 0;
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1683_ = crate::leanh::lean_ctor_get(v___y_1680_, 5);
                v___x_1684_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msg_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
                v_a_1685_ = crate::leanh::lean_ctor_get(v___x_1684_, 0);
                v_isSharedCheck_1729_ = (!crate::leanh::lean_is_exclusive(v___x_1684_)) as u8;
                if v_isSharedCheck_1729_ == 0 {
                    v___x_1687_ = v___x_1684_;
                    v_isShared_1688_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1685_);
                    crate::leanh::lean_dec(v___x_1684_);
                    v___x_1687_ = crate::leanh::lean_box(0);
                    v_isShared_1688_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1689_ = lean_st_ref_take(v___y_1681_);
                v_traceState_1690_ = crate::leanh::lean_ctor_get(v___x_1689_, 4);
                v_env_1691_ = crate::leanh::lean_ctor_get(v___x_1689_, 0);
                v_nextMacroScope_1692_ = crate::leanh::lean_ctor_get(v___x_1689_, 1);
                v_ngen_1693_ = crate::leanh::lean_ctor_get(v___x_1689_, 2);
                v_auxDeclNGen_1694_ = crate::leanh::lean_ctor_get(v___x_1689_, 3);
                v_cache_1695_ = crate::leanh::lean_ctor_get(v___x_1689_, 5);
                v_messages_1696_ = crate::leanh::lean_ctor_get(v___x_1689_, 6);
                v_infoState_1697_ = crate::leanh::lean_ctor_get(v___x_1689_, 7);
                v_snapshotTasks_1698_ = crate::leanh::lean_ctor_get(v___x_1689_, 8);
                v_isSharedCheck_1728_ = (!crate::leanh::lean_is_exclusive(v___x_1689_)) as u8;
                if v_isSharedCheck_1728_ == 0 {
                    v___x_1700_ = v___x_1689_;
                    v_isShared_1701_ = v_isSharedCheck_1728_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1698_);
                    crate::leanh::lean_inc(v_infoState_1697_);
                    crate::leanh::lean_inc(v_messages_1696_);
                    crate::leanh::lean_inc(v_cache_1695_);
                    crate::leanh::lean_inc(v_traceState_1690_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1694_);
                    crate::leanh::lean_inc(v_ngen_1693_);
                    crate::leanh::lean_inc(v_nextMacroScope_1692_);
                    crate::leanh::lean_inc(v_env_1691_);
                    crate::leanh::lean_dec(v___x_1689_);
                    v___x_1700_ = crate::leanh::lean_box(0);
                    v_isShared_1701_ = v_isSharedCheck_1728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1702_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1690_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1703_ = crate::leanh::lean_ctor_get(v_traceState_1690_, 0);
                v_isSharedCheck_1727_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1690_)) as u8;
                if v_isSharedCheck_1727_ == 0 {
                    v___x_1705_ = v_traceState_1690_;
                    v_isShared_1706_ = v_isSharedCheck_1727_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1703_);
                    crate::leanh::lean_dec(v_traceState_1690_);
                    v___x_1705_ = crate::leanh::lean_box(0);
                    v_isShared_1706_ = v_isSharedCheck_1727_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1707_ = crate::leanh::lean_box(0);
                v___x_1708_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0);
                v___x_1709_ = 0;
                v___x_1710_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1;
                v___x_1711_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_1711_, 0, v_cls_1676_);
                crate::leanh::lean_ctor_set(v___x_1711_, 1, v___x_1707_);
                crate::leanh::lean_ctor_set(v___x_1711_, 2, v___x_1710_);
                crate::leanh::lean_ctor_set_float(
                    v___x_1711_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1708_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_1711_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1708_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1711_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1709_,
                );
                v___x_1712_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2;
                v___x_1713_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1713_, 0, v___x_1711_);
                crate::leanh::lean_ctor_set(v___x_1713_, 1, v_a_1685_);
                crate::leanh::lean_ctor_set(v___x_1713_, 2, v___x_1712_);
                crate::leanh::lean_inc(v_ref_1683_);
                v___x_1714_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1714_, 0, v_ref_1683_);
                crate::leanh::lean_ctor_set(v___x_1714_, 1, v___x_1713_);
                v___x_1715_ = l_Lean_PersistentArray_push___redArg(v_traces_1703_, v___x_1714_);
                if v_isShared_1706_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1705_, 0, v___x_1715_);
                    v___x_1717_ = v___x_1705_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1715_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1726_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1702_,
                    );
                    v___x_1717_ = v_reuseFailAlloc_1726_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1701_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1700_, 4, v___x_1717_);
                    v___x_1719_ = v___x_1700_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1725_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_env_1691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_nextMacroScope_1692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_ngen_1693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_auxDeclNGen_1694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 4, v___x_1717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 5, v_cache_1695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 6, v_messages_1696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 7, v_infoState_1697_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 8, v_snapshotTasks_1698_);
                    v___x_1719_ = v_reuseFailAlloc_1725_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1720_ = lean_st_ref_set(v___y_1681_, v___x_1719_);
                v___x_1721_ = crate::leanh::lean_box(0);
                if v_isShared_1688_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1687_, 0, v___x_1721_);
                    v___x_1723_ = v___x_1687_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
                    v___x_1723_ = v_reuseFailAlloc_1724_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___boxed(
    mut v_cls_1730_: *mut crate::leanh::LeanObject,
    mut v_msg_1731_: *mut crate::leanh::LeanObject,
    mut v___y_1732_: *mut crate::leanh::LeanObject,
    mut v___y_1733_: *mut crate::leanh::LeanObject,
    mut v___y_1734_: *mut crate::leanh::LeanObject,
    mut v___y_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1737_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(
        v_cls_1730_,
        v_msg_1731_,
        v___y_1732_,
        v___y_1733_,
        v___y_1734_,
        v___y_1735_,
    );
    crate::leanh::lean_dec(v___y_1735_);
    crate::leanh::lean_dec_ref(v___y_1734_);
    crate::leanh::lean_dec(v___y_1733_);
    crate::leanh::lean_dec_ref(v___y_1732_);
    return v_res_1737_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkInjEq___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Lean_Meta_Grind_mkInjEq___closed__3;
    v___x_1749_ = l_Lean_Meta_Grind_mkInjEq___closed__5;
    v___x_1750_ = l_Lean_Name_append(v___x_1749_, v___x_1748_);
    return v___x_1750_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkInjEq___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1752_ = l_Lean_Meta_Grind_mkInjEq___closed__7;
    v___x_1753_ = l_Lean_stringToMessageData(v___x_1752_);
    return v___x_1753_;
}
pub unsafe fn l_Lean_Meta_Grind_mkInjEq(
    mut v_e_1754_: *mut crate::leanh::LeanObject,
    mut v_a_1755_: *mut crate::leanh::LeanObject,
    mut v_a_1756_: *mut crate::leanh::LeanObject,
    mut v_a_1757_: *mut crate::leanh::LeanObject,
    mut v_a_1758_: *mut crate::leanh::LeanObject,
    mut v_a_1759_: *mut crate::leanh::LeanObject,
    mut v_a_1760_: *mut crate::leanh::LeanObject,
    mut v_a_1761_: *mut crate::leanh::LeanObject,
    mut v_a_1762_: *mut crate::leanh::LeanObject,
    mut v_a_1763_: *mut crate::leanh::LeanObject,
    mut v_a_1764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v_val_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: u8 = 0;
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1795_: u8 = 0;
    let mut v_inheritedTraceOptions_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_isSharedCheck_1816_: u8 = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut v_a_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1825_: u8 = 0;
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1829_: u8 = 0;
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_1754_) == 5 {
                    v_fn_1766_ = crate::leanh::lean_ctor_get(v_e_1754_, 0);
                    v_arg_1767_ = crate::leanh::lean_ctor_get(v_e_1754_, 1);
                    crate::leanh::lean_inc_ref_n(v_arg_1767_, 2);
                    crate::leanh::lean_inc_ref(v_fn_1766_);
                    v___x_1768_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_fn_1766_, v_arg_1767_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
                    if crate::leanh::lean_obj_tag(v___x_1768_) == 0 {
                        v_a_1769_ = crate::leanh::lean_ctor_get(v___x_1768_, 0);
                        v_isSharedCheck_1821_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1768_)) as u8;
                        if v_isSharedCheck_1821_ == 0 {
                            v___x_1771_ = v___x_1768_;
                            v_isShared_1772_ = v_isSharedCheck_1821_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1769_);
                            crate::leanh::lean_dec(v___x_1768_);
                            v___x_1771_ = crate::leanh::lean_box(0);
                            v_isShared_1772_ = v_isSharedCheck_1821_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_arg_1767_);
                        crate::leanh::lean_dec_ref_known(v_e_1754_, 2);
                        v_a_1822_ = crate::leanh::lean_ctor_get(v___x_1768_, 0);
                        v_isSharedCheck_1829_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1768_)) as u8;
                        if v_isSharedCheck_1829_ == 0 {
                            v___x_1824_ = v___x_1768_;
                            v_isShared_1825_ = v_isSharedCheck_1829_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1822_);
                            crate::leanh::lean_dec(v___x_1768_);
                            v___x_1824_ = crate::leanh::lean_box(0);
                            v_isShared_1825_ = v_isSharedCheck_1829_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1754_);
                    v___x_1830_ = crate::leanh::lean_box(0);
                    v___x_1831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1831_, 0, v___x_1830_);
                    return v___x_1831_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1769_) == 1 {
                    crate::leanh::lean_del_object(v___x_1771_);
                    v_val_1773_ = crate::leanh::lean_ctor_get(v_a_1769_, 0);
                    crate::leanh::lean_inc(v_val_1773_);
                    crate::leanh::lean_dec_ref_known(v_a_1769_, 1);
                    v_fst_1774_ = crate::leanh::lean_ctor_get(v_val_1773_, 0);
                    v_snd_1775_ = crate::leanh::lean_ctor_get(v_val_1773_, 1);
                    v_isSharedCheck_1816_ = (!crate::leanh::lean_is_exclusive(v_val_1773_)) as u8;
                    if v_isSharedCheck_1816_ == 0 {
                        v___x_1777_ = v_val_1773_;
                        v_isShared_1778_ = v_isSharedCheck_1816_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1775_);
                        crate::leanh::lean_inc(v_fst_1774_);
                        crate::leanh::lean_dec(v_val_1773_);
                        v___x_1777_ = crate::leanh::lean_box(0);
                        v_isShared_1778_ = v_isSharedCheck_1816_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1769_);
                    crate::leanh::lean_dec_ref(v_arg_1767_);
                    crate::leanh::lean_dec_ref_known(v_e_1754_, 2);
                    v___x_1817_ = crate::leanh::lean_box(0);
                    if v_isShared_1772_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1771_, 0, v___x_1817_);
                        v___x_1819_ = v___x_1771_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                        v___x_1819_ = v_reuseFailAlloc_1820_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1779_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1754_, v_a_1755_);
                if crate::leanh::lean_obj_tag(v___x_1779_) == 0 {
                    v_a_1780_ = crate::leanh::lean_ctor_get(v___x_1779_, 0);
                    crate::leanh::lean_inc(v_a_1780_);
                    crate::leanh::lean_dec_ref_known(v___x_1779_, 1);
                    v___x_1781_ = l_Lean_Expr_app___override(v_fst_1774_, v_e_1754_);
                    v___x_1792_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_a_1764_);
                    crate::leanh::lean_inc_ref(v_a_1763_);
                    crate::leanh::lean_inc(v_a_1762_);
                    crate::leanh::lean_inc_ref(v_a_1761_);
                    crate::leanh::lean_inc(v_a_1760_);
                    crate::leanh::lean_inc_ref(v_a_1759_);
                    crate::leanh::lean_inc(v_a_1758_);
                    crate::leanh::lean_inc_ref(v_a_1757_);
                    crate::leanh::lean_inc(v_a_1756_);
                    crate::leanh::lean_inc(v_a_1755_);
                    crate::leanh::lean_inc_ref(v___x_1781_);
                    v___x_1793_ = lean_grind_internalize(
                        v___x_1781_,
                        v_a_1780_,
                        v___x_1792_,
                        v_a_1755_,
                        v_a_1756_,
                        v_a_1757_,
                        v_a_1758_,
                        v_a_1759_,
                        v_a_1760_,
                        v_a_1761_,
                        v_a_1762_,
                        v_a_1763_,
                        v_a_1764_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1793_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1793_, 1);
                        v_options_1794_ = crate::leanh::lean_ctor_get(v_a_1763_, 2);
                        v_hasTrace_1795_ = crate::leanh::lean_ctor_get_uint8(
                            v_options_1794_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_1795_ == 0 {
                            crate::leanh::lean_del_object(v___x_1777_);
                            v___y_1783_ = v_a_1755_;
                            v___y_1784_ = v_a_1757_;
                            v___y_1785_ = v_a_1761_;
                            v___y_1786_ = v_a_1762_;
                            v___y_1787_ = v_a_1763_;
                            v___y_1788_ = v_a_1764_;
                            state = 3;
                            continue;
                        } else {
                            v_inheritedTraceOptions_1796_ =
                                crate::leanh::lean_ctor_get(v_a_1763_, 13);
                            v___x_1797_ = l_Lean_Meta_Grind_mkInjEq___closed__3;
                            v___x_1798_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkInjEq___closed__6),
                                core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkInjEq___closed__6_once),
                                _init_l_Lean_Meta_Grind_mkInjEq___closed__6,
                            );
                            v___x_1799_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_1796_,
                                v_options_1794_,
                                v___x_1798_,
                            );
                            if v___x_1799_ == 0 {
                                crate::leanh::lean_del_object(v___x_1777_);
                                v___y_1783_ = v_a_1755_;
                                v___y_1784_ = v_a_1757_;
                                v___y_1785_ = v_a_1761_;
                                v___y_1786_ = v_a_1762_;
                                v___y_1787_ = v_a_1763_;
                                v___y_1788_ = v_a_1764_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v___x_1781_);
                                v___x_1800_ = l_Lean_MessageData_ofExpr(v___x_1781_);
                                v___x_1801_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkInjEq___closed__8),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_mkInjEq___closed__8_once
                                    ),
                                    _init_l_Lean_Meta_Grind_mkInjEq___closed__8,
                                );
                                if v_isShared_1778_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_1777_, 7);
                                    crate::leanh::lean_ctor_set(v___x_1777_, 1, v___x_1801_);
                                    crate::leanh::lean_ctor_set(v___x_1777_, 0, v___x_1800_);
                                    v___x_1803_ = v___x_1777_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1807_ =
                                        crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1807_,
                                        0,
                                        v___x_1800_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1807_,
                                        1,
                                        v___x_1801_,
                                    );
                                    v___x_1803_ = v_reuseFailAlloc_1807_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1781_);
                        crate::leanh::lean_del_object(v___x_1777_);
                        crate::leanh::lean_dec(v_snd_1775_);
                        crate::leanh::lean_dec_ref(v_arg_1767_);
                        return v___x_1793_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1777_);
                    crate::leanh::lean_dec(v_snd_1775_);
                    crate::leanh::lean_dec(v_fst_1774_);
                    crate::leanh::lean_dec_ref(v_arg_1767_);
                    crate::leanh::lean_dec_ref_known(v_e_1754_, 2);
                    v_a_1808_ = crate::leanh::lean_ctor_get(v___x_1779_, 0);
                    v_isSharedCheck_1815_ = (!crate::leanh::lean_is_exclusive(v___x_1779_)) as u8;
                    if v_isSharedCheck_1815_ == 0 {
                        v___x_1810_ = v___x_1779_;
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1808_);
                        crate::leanh::lean_dec(v___x_1779_);
                        v___x_1810_ = crate::leanh::lean_box(0);
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v_arg_1767_);
                v___x_1789_ = l_Lean_Expr_app___override(v_snd_1775_, v_arg_1767_);
                v___x_1790_ = 0;
                v___x_1791_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                    v___x_1781_,
                    v_arg_1767_,
                    v___x_1789_,
                    v___x_1790_,
                    v___y_1783_,
                    v___y_1784_,
                    v___y_1785_,
                    v___y_1786_,
                    v___y_1787_,
                    v___y_1788_,
                );
                return v___x_1791_;
            }
            4 => {
                crate::leanh::lean_inc_ref(v_arg_1767_);
                v___x_1804_ = l_Lean_MessageData_ofExpr(v_arg_1767_);
                v___x_1805_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1805_, 0, v___x_1803_);
                crate::leanh::lean_ctor_set(v___x_1805_, 1, v___x_1804_);
                v___x_1806_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(
                    v___x_1797_,
                    v___x_1805_,
                    v_a_1761_,
                    v_a_1762_,
                    v_a_1763_,
                    v_a_1764_,
                );
                if crate::leanh::lean_obj_tag(v___x_1806_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1806_, 1);
                    v___y_1783_ = v_a_1755_;
                    v___y_1784_ = v_a_1757_;
                    v___y_1785_ = v_a_1761_;
                    v___y_1786_ = v_a_1762_;
                    v___y_1787_ = v_a_1763_;
                    v___y_1788_ = v_a_1764_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_1781_);
                    crate::leanh::lean_dec(v_snd_1775_);
                    crate::leanh::lean_dec_ref(v_arg_1767_);
                    return v___x_1806_;
                }
            }
            5 => {
                if v_isShared_1811_ == 0 {
                    v___x_1813_ = v___x_1810_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1814_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
                    v___x_1813_ = v_reuseFailAlloc_1814_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1813_;
            }
            7 => {
                return v___x_1819_;
            }
            8 => {
                if v_isShared_1825_ == 0 {
                    v___x_1827_ = v___x_1824_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1828_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
                    v___x_1827_ = v_reuseFailAlloc_1828_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1827_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkInjEq___boxed(
    mut v_e_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
    mut v_a_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
    mut v_a_1841_: *mut crate::leanh::LeanObject,
    mut v_a_1842_: *mut crate::leanh::LeanObject,
    mut v_a_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1844_ = l_Lean_Meta_Grind_mkInjEq(
        v_e_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_,
        v_a_1840_, v_a_1841_, v_a_1842_,
    );
    crate::leanh::lean_dec(v_a_1842_);
    crate::leanh::lean_dec_ref(v_a_1841_);
    crate::leanh::lean_dec(v_a_1840_);
    crate::leanh::lean_dec_ref(v_a_1839_);
    crate::leanh::lean_dec(v_a_1838_);
    crate::leanh::lean_dec_ref(v_a_1837_);
    crate::leanh::lean_dec(v_a_1836_);
    crate::leanh::lean_dec_ref(v_a_1835_);
    crate::leanh::lean_dec(v_a_1834_);
    crate::leanh::lean_dec(v_a_1833_);
    return v_res_1844_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(
    mut v_cls_1845_: *mut crate::leanh::LeanObject,
    mut v_msg_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
    mut v___y_1849_: *mut crate::leanh::LeanObject,
    mut v___y_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1858_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(
        v_cls_1845_,
        v_msg_1846_,
        v___y_1853_,
        v___y_1854_,
        v___y_1855_,
        v___y_1856_,
    );
    return v___x_1858_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___boxed(
    mut v_cls_1859_: *mut crate::leanh::LeanObject,
    mut v_msg_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
    mut v___y_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(
        v_cls_1859_,
        v_msg_1860_,
        v___y_1861_,
        v___y_1862_,
        v___y_1863_,
        v___y_1864_,
        v___y_1865_,
        v___y_1866_,
        v___y_1867_,
        v___y_1868_,
        v___y_1869_,
        v___y_1870_,
    );
    crate::leanh::lean_dec(v___y_1870_);
    crate::leanh::lean_dec_ref(v___y_1869_);
    crate::leanh::lean_dec(v___y_1868_);
    crate::leanh::lean_dec_ref(v___y_1867_);
    crate::leanh::lean_dec(v___y_1866_);
    crate::leanh::lean_dec_ref(v___y_1865_);
    crate::leanh::lean_dec(v___y_1864_);
    crate::leanh::lean_dec_ref(v___y_1863_);
    crate::leanh::lean_dec(v___y_1862_);
    crate::leanh::lean_dec(v___y_1861_);
    return v_res_1872_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(
    mut v_keys_1873_: *mut crate::leanh::LeanObject,
    mut v_vals_1874_: *mut crate::leanh::LeanObject,
    mut v_i_1875_: *mut crate::leanh::LeanObject,
    mut v_k_1876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: u8 = 0;
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1877_ = lean_array_get_size(v_keys_1873_);
                v___x_1878_ = lean_nat_dec_lt(v_i_1875_, v___x_1877_);
                if v___x_1878_ == 0 {
                    crate::leanh::lean_dec(v_i_1875_);
                    v___x_1879_ = crate::leanh::lean_box(0);
                    return v___x_1879_;
                } else {
                    v_k_x27_1880_ = lean_array_fget_borrowed(v_keys_1873_, v_i_1875_);
                    v___x_1881_ = l_Lean_instBEqHeadIndex_beq(v_k_1876_, v_k_x27_1880_);
                    if v___x_1881_ == 0 {
                        v___x_1882_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1883_ = lean_nat_add(v_i_1875_, v___x_1882_);
                        crate::leanh::lean_dec(v_i_1875_);
                        v_i_1875_ = v___x_1883_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1885_ = lean_array_fget_borrowed(v_vals_1874_, v_i_1875_);
                        crate::leanh::lean_dec(v_i_1875_);
                        crate::leanh::lean_inc(v___x_1885_);
                        v___x_1886_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1886_, 0, v___x_1885_);
                        return v___x_1886_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_keys_1887_: *mut crate::leanh::LeanObject,
    mut v_vals_1888_: *mut crate::leanh::LeanObject,
    mut v_i_1889_: *mut crate::leanh::LeanObject,
    mut v_k_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1891_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_1887_, v_vals_1888_, v_i_1889_, v_k_1890_);
    crate::leanh::lean_dec(v_k_1890_);
    crate::leanh::lean_dec_ref(v_vals_1888_);
    crate::leanh::lean_dec_ref(v_keys_1887_);
    return v_res_1891_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(
    mut v_x_1892_: *mut crate::leanh::LeanObject,
    mut v_x_1893_: usize,
    mut v_x_1894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: usize = 0;
    let mut v___x_1898_: usize = 0;
    let mut v___x_1899_: usize = 0;
    let mut v_j_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: usize = 0;
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1892_) == 0 {
                    v_es_1895_ = crate::leanh::lean_ctor_get(v_x_1892_, 0);
                    v___x_1896_ = crate::leanh::lean_box(2);
                    v___x_1897_ = 5usize;
                    v___x_1898_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
                    v___x_1899_ = lean_usize_land(v_x_1893_, v___x_1898_);
                    v_j_1900_ = lean_usize_to_nat(v___x_1899_);
                    v___x_1901_ = lean_array_get_borrowed(v___x_1896_, v_es_1895_, v_j_1900_);
                    crate::leanh::lean_dec(v_j_1900_);
                    match crate::leanh::lean_obj_tag(v___x_1901_) {
                        0 => {
                            v_key_1902_ = crate::leanh::lean_ctor_get(v___x_1901_, 0);
                            v_val_1903_ = crate::leanh::lean_ctor_get(v___x_1901_, 1);
                            v___x_1904_ = l_Lean_instBEqHeadIndex_beq(v_x_1894_, v_key_1902_);
                            if v___x_1904_ == 0 {
                                v___x_1905_ = crate::leanh::lean_box(0);
                                return v___x_1905_;
                            } else {
                                crate::leanh::lean_inc(v_val_1903_);
                                v___x_1906_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1906_, 0, v_val_1903_);
                                return v___x_1906_;
                            }
                        }
                        1 => {
                            v_node_1907_ = crate::leanh::lean_ctor_get(v___x_1901_, 0);
                            v___x_1908_ = lean_usize_shift_right(v_x_1893_, v___x_1897_);
                            v_x_1892_ = v_node_1907_;
                            v_x_1893_ = v___x_1908_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1910_ = crate::leanh::lean_box(0);
                            return v___x_1910_;
                        }
                    }
                } else {
                    v_ks_1911_ = crate::leanh::lean_ctor_get(v_x_1892_, 0);
                    v_vs_1912_ = crate::leanh::lean_ctor_get(v_x_1892_, 1);
                    v___x_1913_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1914_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_ks_1911_, v_vs_1912_, v___x_1913_, v_x_1894_);
                    return v___x_1914_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg___boxed(
    mut v_x_1915_: *mut crate::leanh::LeanObject,
    mut v_x_1916_: *mut crate::leanh::LeanObject,
    mut v_x_1917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9714__boxed_1918_: usize = 0;
    let mut v_res_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9714__boxed_1918_ = crate::leanh::lean_unbox_usize(v_x_1916_);
    crate::leanh::lean_dec(v_x_1916_);
    v_res_1919_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_1915_, v_x_9714__boxed_1918_, v_x_1917_);
    crate::leanh::lean_dec(v_x_1917_);
    crate::leanh::lean_dec_ref(v_x_1915_);
    return v_res_1919_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(
    mut v_x_1920_: *mut crate::leanh::LeanObject,
    mut v_x_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1922_: u64 = 0;
    let mut v___x_1923_: usize = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1922_ = l_Lean_HeadIndex_hash(v_x_1921_);
    v___x_1923_ = lean_uint64_to_usize(v___x_1922_);
    v___x_1924_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_1920_, v___x_1923_, v_x_1921_);
    return v___x_1924_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg___boxed(
    mut v_x_1925_: *mut crate::leanh::LeanObject,
    mut v_x_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1927_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_1925_, v_x_1926_);
    crate::leanh::lean_dec(v_x_1926_);
    crate::leanh::lean_dec_ref(v_x_1925_);
    return v_res_1927_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(
    mut v_f_1928_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1929_: *mut crate::leanh::LeanObject,
    mut v_b_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
    mut v___y_1933_: *mut crate::leanh::LeanObject,
    mut v___y_1934_: *mut crate::leanh::LeanObject,
    mut v___y_1935_: *mut crate::leanh::LeanObject,
    mut v___y_1936_: *mut crate::leanh::LeanObject,
    mut v___y_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1947_: u8 = 0;
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_1929_) == 0 {
                    v___x_1942_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1942_, 0, v_b_1930_);
                    return v___x_1942_;
                } else {
                    v_head_1943_ = crate::leanh::lean_ctor_get(v_as_x27_1929_, 0);
                    v_tail_1944_ = crate::leanh::lean_ctor_get(v_as_x27_1929_, 1);
                    v___x_1945_ = crate::leanh::lean_box(0);
                    v___x_1951_ = l_Lean_Expr_isApp(v_head_1943_);
                    if v___x_1951_ == 0 {
                        v___y_1947_ = v___x_1951_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1952_ = l_Lean_Expr_appFn_x21(v_head_1943_);
                        v___x_1953_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v___x_1952_,
                                v_f_1928_,
                            );
                        crate::leanh::lean_dec_ref(v___x_1952_);
                        v___y_1947_ = v___x_1953_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1947_ == 0 {
                    v_as_x27_1929_ = v_tail_1944_;
                    v_b_1930_ = v___x_1945_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_head_1943_);
                    v___x_1949_ = l_Lean_Meta_Grind_mkInjEq(
                        v_head_1943_,
                        v___y_1931_,
                        v___y_1932_,
                        v___y_1933_,
                        v___y_1934_,
                        v___y_1935_,
                        v___y_1936_,
                        v___y_1937_,
                        v___y_1938_,
                        v___y_1939_,
                        v___y_1940_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1949_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1949_, 1);
                        v_as_x27_1929_ = v_tail_1944_;
                        v_b_1930_ = v___x_1945_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1949_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg___boxed(
    mut v_f_1954_: *mut crate::leanh::LeanObject,
    mut v_as_x27_1955_: *mut crate::leanh::LeanObject,
    mut v_b_1956_: *mut crate::leanh::LeanObject,
    mut v___y_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
    mut v___y_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1968_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_1954_, v_as_x27_1955_, v_b_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
    crate::leanh::lean_dec(v___y_1966_);
    crate::leanh::lean_dec_ref(v___y_1965_);
    crate::leanh::lean_dec(v___y_1964_);
    crate::leanh::lean_dec_ref(v___y_1963_);
    crate::leanh::lean_dec(v___y_1962_);
    crate::leanh::lean_dec_ref(v___y_1961_);
    crate::leanh::lean_dec(v___y_1960_);
    crate::leanh::lean_dec_ref(v___y_1959_);
    crate::leanh::lean_dec(v___y_1958_);
    crate::leanh::lean_dec(v___y_1957_);
    crate::leanh::lean_dec(v_as_x27_1955_);
    crate::leanh::lean_dec_ref(v_f_1954_);
    return v_res_1968_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(
    mut v_us_1969_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1970_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1971_: *mut crate::leanh::LeanObject,
    mut v_f_1972_: *mut crate::leanh::LeanObject,
    mut v_h_1973_: *mut crate::leanh::LeanObject,
    mut v_a_1974_: *mut crate::leanh::LeanObject,
    mut v_a_1975_: *mut crate::leanh::LeanObject,
    mut v_a_1976_: *mut crate::leanh::LeanObject,
    mut v_a_1977_: *mut crate::leanh::LeanObject,
    mut v_a_1978_: *mut crate::leanh::LeanObject,
    mut v_a_1979_: *mut crate::leanh::LeanObject,
    mut v_a_1980_: *mut crate::leanh::LeanObject,
    mut v_a_1981_: *mut crate::leanh::LeanObject,
    mut v_a_1982_: *mut crate::leanh::LeanObject,
    mut v_a_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1991_: u8 = 0;
    let mut v_nextDeclIdx_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newFacts_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_2000_: u8 = 0;
    let mut v_nextIdx_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sstates_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v_thms_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fns_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_unused_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_unused_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v_unused_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1985_ = lean_st_ref_take(v_a_1974_);
                v_toGoalState_1986_ = crate::leanh::lean_ctor_get(v___x_1985_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_1986_);
                v_inj_1987_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 13);
                crate::leanh::lean_inc_ref(v_inj_1987_);
                v_mvarId_1988_ = crate::leanh::lean_ctor_get(v___x_1985_, 1);
                v_isSharedCheck_2052_ = (!crate::leanh::lean_is_exclusive(v___x_1985_)) as u8;
                if v_isSharedCheck_2052_ == 0 {
                    v_unused_2053_ = crate::leanh::lean_ctor_get(v___x_1985_, 0);
                    crate::leanh::lean_dec(v_unused_2053_);
                    v___x_1990_ = v___x_1985_;
                    v_isShared_1991_ = v_isSharedCheck_2052_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_1988_);
                    crate::leanh::lean_dec(v___x_1985_);
                    v___x_1990_ = crate::leanh::lean_box(0);
                    v_isShared_1991_ = v_isSharedCheck_2052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_nextDeclIdx_1992_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 0);
                v_enodeMap_1993_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 1);
                v_exprs_1994_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 2);
                v_parents_1995_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 3);
                v_congrTable_1996_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 4);
                v_appMap_1997_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 5);
                v_indicesFound_1998_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 6);
                v_newFacts_1999_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 7);
                v_inconsistent_2000_ = crate::leanh::lean_ctor_get_uint8(
                    v_toGoalState_1986_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_nextIdx_2001_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 8);
                v_newRawFacts_2002_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 9);
                v_facts_2003_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 10);
                v_extThms_2004_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 11);
                v_ematch_2005_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 12);
                v_split_2006_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 14);
                v_clean_2007_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 15);
                v_sstates_2008_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 16);
                v_isSharedCheck_2050_ =
                    (!crate::leanh::lean_is_exclusive(v_toGoalState_1986_)) as u8;
                if v_isSharedCheck_2050_ == 0 {
                    v_unused_2051_ = crate::leanh::lean_ctor_get(v_toGoalState_1986_, 13);
                    crate::leanh::lean_dec(v_unused_2051_);
                    v___x_2010_ = v_toGoalState_1986_;
                    v_isShared_2011_ = v_isSharedCheck_2050_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_sstates_2008_);
                    crate::leanh::lean_inc(v_clean_2007_);
                    crate::leanh::lean_inc(v_split_2006_);
                    crate::leanh::lean_inc(v_ematch_2005_);
                    crate::leanh::lean_inc(v_extThms_2004_);
                    crate::leanh::lean_inc(v_facts_2003_);
                    crate::leanh::lean_inc(v_newRawFacts_2002_);
                    crate::leanh::lean_inc(v_nextIdx_2001_);
                    crate::leanh::lean_inc(v_newFacts_1999_);
                    crate::leanh::lean_inc(v_indicesFound_1998_);
                    crate::leanh::lean_inc(v_appMap_1997_);
                    crate::leanh::lean_inc(v_congrTable_1996_);
                    crate::leanh::lean_inc(v_parents_1995_);
                    crate::leanh::lean_inc(v_exprs_1994_);
                    crate::leanh::lean_inc(v_enodeMap_1993_);
                    crate::leanh::lean_inc(v_nextDeclIdx_1992_);
                    crate::leanh::lean_dec(v_toGoalState_1986_);
                    v___x_2010_ = crate::leanh::lean_box(0);
                    v_isShared_2011_ = v_isSharedCheck_2050_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_thms_2012_ = crate::leanh::lean_ctor_get(v_inj_1987_, 0);
                v_fns_2013_ = crate::leanh::lean_ctor_get(v_inj_1987_, 1);
                v_isSharedCheck_2049_ = (!crate::leanh::lean_is_exclusive(v_inj_1987_)) as u8;
                if v_isSharedCheck_2049_ == 0 {
                    v___x_2015_ = v_inj_1987_;
                    v_isShared_2016_ = v_isSharedCheck_2049_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fns_2013_);
                    crate::leanh::lean_inc(v_thms_2012_);
                    crate::leanh::lean_dec(v_inj_1987_);
                    v___x_2015_ = crate::leanh::lean_box(0);
                    v_isShared_2016_ = v_isSharedCheck_2049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2017_ = crate::leanh::lean_box(0);
                v___x_2018_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2018_, 0, v_us_1969_);
                crate::leanh::lean_ctor_set(v___x_2018_, 1, v_00_u03b1_1970_);
                crate::leanh::lean_ctor_set(v___x_2018_, 2, v_00_u03b2_1971_);
                crate::leanh::lean_ctor_set(v___x_2018_, 3, v_h_1973_);
                crate::leanh::lean_ctor_set(v___x_2018_, 4, v___x_2017_);
                crate::leanh::lean_inc_ref(v_f_1972_);
                v___x_2019_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_2013_, v_f_1972_, v___x_2018_);
                if v_isShared_2016_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2015_, 1, v___x_2019_);
                    v___x_2021_ = v___x_2015_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_thms_2012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2019_);
                    v___x_2021_ = v_reuseFailAlloc_2048_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2011_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2010_, 13, v___x_2021_);
                    v___x_2023_ = v___x_2010_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2047_ = crate::leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_nextDeclIdx_1992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_enodeMap_1993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_exprs_1994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_parents_1995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 4, v_congrTable_1996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 5, v_appMap_1997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 6, v_indicesFound_1998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 7, v_newFacts_1999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 8, v_nextIdx_2001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 9, v_newRawFacts_2002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 10, v_facts_2003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 11, v_extThms_2004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 12, v_ematch_2005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 13, v___x_2021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 14, v_split_2006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 15, v_clean_2007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 16, v_sstates_2008_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2047_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_inconsistent_2000_,
                    );
                    v___x_2023_ = v_reuseFailAlloc_2047_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1991_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1990_, 0, v___x_2023_);
                    v___x_2025_ = v___x_1990_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2046_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_mvarId_1988_);
                    v___x_2025_ = v_reuseFailAlloc_2046_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2026_ = lean_st_ref_set(v_a_1974_, v___x_2025_);
                v___x_2027_ = lean_st_ref_get(v_a_1974_);
                v_toGoalState_2040_ = crate::leanh::lean_ctor_get(v___x_2027_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_2040_);
                crate::leanh::lean_dec(v___x_2027_);
                v_appMap_2041_ = crate::leanh::lean_ctor_get(v_toGoalState_2040_, 5);
                crate::leanh::lean_inc_ref(v_appMap_2041_);
                crate::leanh::lean_dec_ref(v_toGoalState_2040_);
                crate::leanh::lean_inc_ref(v_f_1972_);
                v___x_2042_ = l_Lean_Expr_toHeadIndex(v_f_1972_);
                v___x_2043_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_appMap_2041_, v___x_2042_);
                crate::leanh::lean_dec(v___x_2042_);
                crate::leanh::lean_dec_ref(v_appMap_2041_);
                if crate::leanh::lean_obj_tag(v___x_2043_) == 0 {
                    v___x_2044_ = crate::leanh::lean_box(0);
                    v___y_2029_ = v___x_2044_;
                    state = 7;
                    continue;
                } else {
                    v_val_2045_ = crate::leanh::lean_ctor_get(v___x_2043_, 0);
                    crate::leanh::lean_inc(v_val_2045_);
                    crate::leanh::lean_dec_ref_known(v___x_2043_, 1);
                    v___y_2029_ = v_val_2045_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2030_ = crate::leanh::lean_box(0);
                v___x_2031_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_1972_, v___y_2029_, v___x_2030_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
                crate::leanh::lean_dec(v___y_2029_);
                crate::leanh::lean_dec_ref(v_f_1972_);
                if crate::leanh::lean_obj_tag(v___x_2031_) == 0 {
                    v_isSharedCheck_2038_ = (!crate::leanh::lean_is_exclusive(v___x_2031_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v_unused_2039_ = crate::leanh::lean_ctor_get(v___x_2031_, 0);
                        crate::leanh::lean_dec(v_unused_2039_);
                        v___x_2033_ = v___x_2031_;
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2031_);
                        v___x_2033_ = crate::leanh::lean_box(0);
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 8;
                        continue;
                    }
                } else {
                    return v___x_2031_;
                }
            }
            8 => {
                if v_isShared_2034_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2033_, 0, v___x_2030_);
                    v___x_2036_ = v___x_2033_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2030_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn___boxed(
    mut v_us_2054_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2055_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2056_: *mut crate::leanh::LeanObject,
    mut v_f_2057_: *mut crate::leanh::LeanObject,
    mut v_h_2058_: *mut crate::leanh::LeanObject,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_a_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
    mut v_a_2065_: *mut crate::leanh::LeanObject,
    mut v_a_2066_: *mut crate::leanh::LeanObject,
    mut v_a_2067_: *mut crate::leanh::LeanObject,
    mut v_a_2068_: *mut crate::leanh::LeanObject,
    mut v_a_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2070_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(
        v_us_2054_,
        v_00_u03b1_2055_,
        v_00_u03b2_2056_,
        v_f_2057_,
        v_h_2058_,
        v_a_2059_,
        v_a_2060_,
        v_a_2061_,
        v_a_2062_,
        v_a_2063_,
        v_a_2064_,
        v_a_2065_,
        v_a_2066_,
        v_a_2067_,
        v_a_2068_,
    );
    crate::leanh::lean_dec(v_a_2068_);
    crate::leanh::lean_dec_ref(v_a_2067_);
    crate::leanh::lean_dec(v_a_2066_);
    crate::leanh::lean_dec_ref(v_a_2065_);
    crate::leanh::lean_dec(v_a_2064_);
    crate::leanh::lean_dec_ref(v_a_2063_);
    crate::leanh::lean_dec(v_a_2062_);
    crate::leanh::lean_dec_ref(v_a_2061_);
    crate::leanh::lean_dec(v_a_2060_);
    crate::leanh::lean_dec(v_a_2059_);
    return v_res_2070_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(
    mut v_f_2071_: *mut crate::leanh::LeanObject,
    mut v_as_2072_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2073_: *mut crate::leanh::LeanObject,
    mut v_b_2074_: *mut crate::leanh::LeanObject,
    mut v_a_2075_: *mut crate::leanh::LeanObject,
    mut v___y_2076_: *mut crate::leanh::LeanObject,
    mut v___y_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
    mut v___y_2082_: *mut crate::leanh::LeanObject,
    mut v___y_2083_: *mut crate::leanh::LeanObject,
    mut v___y_2084_: *mut crate::leanh::LeanObject,
    mut v___y_2085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2087_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_2071_, v_as_x27_2073_, v_b_2074_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
    return v___x_2087_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___boxed(
    mut v_f_2088_: *mut crate::leanh::LeanObject,
    mut v_as_2089_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2090_: *mut crate::leanh::LeanObject,
    mut v_b_2091_: *mut crate::leanh::LeanObject,
    mut v_a_2092_: *mut crate::leanh::LeanObject,
    mut v___y_2093_: *mut crate::leanh::LeanObject,
    mut v___y_2094_: *mut crate::leanh::LeanObject,
    mut v___y_2095_: *mut crate::leanh::LeanObject,
    mut v___y_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
    mut v___y_2098_: *mut crate::leanh::LeanObject,
    mut v___y_2099_: *mut crate::leanh::LeanObject,
    mut v___y_2100_: *mut crate::leanh::LeanObject,
    mut v___y_2101_: *mut crate::leanh::LeanObject,
    mut v___y_2102_: *mut crate::leanh::LeanObject,
    mut v___y_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2104_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(v_f_2088_, v_as_2089_, v_as_x27_2090_, v_b_2091_, v_a_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
    crate::leanh::lean_dec(v___y_2102_);
    crate::leanh::lean_dec_ref(v___y_2101_);
    crate::leanh::lean_dec(v___y_2100_);
    crate::leanh::lean_dec_ref(v___y_2099_);
    crate::leanh::lean_dec(v___y_2098_);
    crate::leanh::lean_dec_ref(v___y_2097_);
    crate::leanh::lean_dec(v___y_2096_);
    crate::leanh::lean_dec_ref(v___y_2095_);
    crate::leanh::lean_dec(v___y_2094_);
    crate::leanh::lean_dec(v___y_2093_);
    crate::leanh::lean_dec(v_as_x27_2090_);
    crate::leanh::lean_dec(v_as_2089_);
    crate::leanh::lean_dec_ref(v_f_2088_);
    return v_res_2104_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(
    mut v_00_u03b2_2105_: *mut crate::leanh::LeanObject,
    mut v_x_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2108_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_2106_, v_x_2107_);
    return v___x_2108_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___boxed(
    mut v_00_u03b2_2109_: *mut crate::leanh::LeanObject,
    mut v_x_2110_: *mut crate::leanh::LeanObject,
    mut v_x_2111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2112_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(v_00_u03b2_2109_, v_x_2110_, v_x_2111_);
    crate::leanh::lean_dec(v_x_2111_);
    crate::leanh::lean_dec_ref(v_x_2110_);
    return v_res_2112_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(
    mut v_00_u03b2_2113_: *mut crate::leanh::LeanObject,
    mut v_x_2114_: *mut crate::leanh::LeanObject,
    mut v_x_2115_: usize,
    mut v_x_2116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2117_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_2114_, v_x_2115_, v_x_2116_);
    return v___x_2117_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___boxed(
    mut v_00_u03b2_2118_: *mut crate::leanh::LeanObject,
    mut v_x_2119_: *mut crate::leanh::LeanObject,
    mut v_x_2120_: *mut crate::leanh::LeanObject,
    mut v_x_2121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9975__boxed_2122_: usize = 0;
    let mut v_res_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9975__boxed_2122_ = crate::leanh::lean_unbox_usize(v_x_2120_);
    crate::leanh::lean_dec(v_x_2120_);
    v_res_2123_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(v_00_u03b2_2118_, v_x_2119_, v_x_9975__boxed_2122_, v_x_2121_);
    crate::leanh::lean_dec(v_x_2121_);
    crate::leanh::lean_dec_ref(v_x_2119_);
    return v_res_2123_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(
    mut v_00_u03b2_2124_: *mut crate::leanh::LeanObject,
    mut v_keys_2125_: *mut crate::leanh::LeanObject,
    mut v_vals_2126_: *mut crate::leanh::LeanObject,
    mut v_heq_2127_: *mut crate::leanh::LeanObject,
    mut v_i_2128_: *mut crate::leanh::LeanObject,
    mut v_k_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_2125_, v_vals_2126_, v_i_2128_, v_k_2129_);
    return v___x_2130_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_2131_: *mut crate::leanh::LeanObject,
    mut v_keys_2132_: *mut crate::leanh::LeanObject,
    mut v_vals_2133_: *mut crate::leanh::LeanObject,
    mut v_heq_2134_: *mut crate::leanh::LeanObject,
    mut v_i_2135_: *mut crate::leanh::LeanObject,
    mut v_k_2136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2137_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(v_00_u03b2_2131_, v_keys_2132_, v_vals_2133_, v_heq_2134_, v_i_2135_, v_k_2136_);
    crate::leanh::lean_dec(v_k_2136_);
    crate::leanh::lean_dec_ref(v_vals_2133_);
    crate::leanh::lean_dec_ref(v_keys_2132_);
    return v_res_2137_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(
    mut v_e_2143_: *mut crate::leanh::LeanObject,
    mut v_a_2144_: *mut crate::leanh::LeanObject,
    mut v_a_2145_: *mut crate::leanh::LeanObject,
    mut v_a_2146_: *mut crate::leanh::LeanObject,
    mut v_a_2147_: *mut crate::leanh::LeanObject,
    mut v_a_2148_: *mut crate::leanh::LeanObject,
    mut v_a_2149_: *mut crate::leanh::LeanObject,
    mut v_a_2150_: *mut crate::leanh::LeanObject,
    mut v_a_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
    mut v_a_2153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: u8 = 0;
    let mut v_arg_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: u8 = 0;
    let mut v_arg_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: u8 = 0;
    let mut v_arg_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2199_: u8 = 0;
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2220_: u8 = 0;
    let mut v_a_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2224_: u8 = 0;
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_isSharedCheck_2229_: u8 = 0;
    let mut v_a_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2233_: u8 = 0;
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2143_);
                v___x_2158_ = l_Lean_Expr_cleanupAnnotations(v_e_2143_);
                v___x_2159_ = l_Lean_Expr_isApp(v___x_2158_);
                if v___x_2159_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2158_);
                    crate::leanh::lean_dec_ref(v_e_2143_);
                    state = 1;
                    continue;
                } else {
                    v_arg_2160_ = crate::leanh::lean_ctor_get(v___x_2158_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2160_);
                    v___x_2161_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2158_);
                    v___x_2162_ = l_Lean_Expr_isApp(v___x_2161_);
                    if v___x_2162_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2161_);
                        crate::leanh::lean_dec_ref(v_arg_2160_);
                        crate::leanh::lean_dec_ref(v_e_2143_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_2163_ = crate::leanh::lean_ctor_get(v___x_2161_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2163_);
                        v___x_2164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2161_);
                        v___x_2165_ = l_Lean_Expr_isApp(v___x_2164_);
                        if v___x_2165_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2164_);
                            crate::leanh::lean_dec_ref(v_arg_2163_);
                            crate::leanh::lean_dec_ref(v_arg_2160_);
                            crate::leanh::lean_dec_ref(v_e_2143_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_2166_ = crate::leanh::lean_ctor_get(v___x_2164_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2166_);
                            v___x_2167_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2164_);
                            v___x_2193_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2;
                            v___x_2194_ = l_Lean_Expr_isConstOf(v___x_2167_, v___x_2193_);
                            if v___x_2194_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2167_);
                                crate::leanh::lean_dec_ref(v_arg_2166_);
                                crate::leanh::lean_dec_ref(v_arg_2163_);
                                crate::leanh::lean_dec_ref(v_arg_2160_);
                                crate::leanh::lean_dec_ref(v_e_2143_);
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_e_2143_);
                                v___x_2195_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                                    v_e_2143_, v_a_2144_, v_a_2148_, v_a_2150_, v_a_2151_,
                                    v_a_2152_, v_a_2153_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2195_) == 0 {
                                    v_a_2196_ = crate::leanh::lean_ctor_get(v___x_2195_, 0);
                                    v_isSharedCheck_2229_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2195_)) as u8;
                                    if v_isSharedCheck_2229_ == 0 {
                                        v___x_2198_ = v___x_2195_;
                                        v_isShared_2199_ = v_isSharedCheck_2229_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2196_);
                                        crate::leanh::lean_dec(v___x_2195_);
                                        v___x_2198_ = crate::leanh::lean_box(0);
                                        v_isShared_2199_ = v_isSharedCheck_2229_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2167_);
                                    crate::leanh::lean_dec_ref(v_arg_2166_);
                                    crate::leanh::lean_dec_ref(v_arg_2163_);
                                    crate::leanh::lean_dec_ref(v_arg_2160_);
                                    crate::leanh::lean_dec_ref(v_e_2143_);
                                    v_a_2230_ = crate::leanh::lean_ctor_get(v___x_2195_, 0);
                                    v_isSharedCheck_2237_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2195_)) as u8;
                                    if v_isSharedCheck_2237_ == 0 {
                                        v___x_2232_ = v___x_2195_;
                                        v_isShared_2233_ = v_isSharedCheck_2237_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2230_);
                                        crate::leanh::lean_dec(v___x_2195_);
                                        v___x_2232_ = crate::leanh::lean_box(0);
                                        v_isShared_2233_ = v_isSharedCheck_2237_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2156_ = crate::leanh::lean_box(0);
                v___x_2157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                return v___x_2157_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_e_2143_);
                v___x_2180_ = l_Lean_Meta_Grind_mkEqTrueProof(
                    v_e_2143_,
                    v___y_2170_,
                    v___y_2171_,
                    v___y_2172_,
                    v___y_2173_,
                    v___y_2174_,
                    v___y_2175_,
                    v___y_2176_,
                    v___y_2177_,
                    v___y_2178_,
                    v___y_2179_,
                );
                if crate::leanh::lean_obj_tag(v___x_2180_) == 0 {
                    v_a_2181_ = crate::leanh::lean_ctor_get(v___x_2180_, 0);
                    crate::leanh::lean_inc(v_a_2181_);
                    crate::leanh::lean_dec_ref_known(v___x_2180_, 1);
                    v___x_2182_ = l_Lean_Expr_constLevels_x21(v___x_2167_);
                    crate::leanh::lean_dec_ref(v___x_2167_);
                    v___x_2183_ = l_Lean_Meta_mkOfEqTrueCore(v_e_2143_, v_a_2181_);
                    v___x_2184_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v___x_2182_, v_arg_2166_, v_arg_2163_, v_f_2169_, v___x_2183_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
                    return v___x_2184_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_2169_);
                    crate::leanh::lean_dec_ref(v___x_2167_);
                    crate::leanh::lean_dec_ref(v_arg_2166_);
                    crate::leanh::lean_dec_ref(v_arg_2163_);
                    crate::leanh::lean_dec_ref(v_e_2143_);
                    v_a_2185_ = crate::leanh::lean_ctor_get(v___x_2180_, 0);
                    v_isSharedCheck_2192_ = (!crate::leanh::lean_is_exclusive(v___x_2180_)) as u8;
                    if v_isSharedCheck_2192_ == 0 {
                        v___x_2187_ = v___x_2180_;
                        v_isShared_2188_ = v_isSharedCheck_2192_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2185_);
                        crate::leanh::lean_dec(v___x_2180_);
                        v___x_2187_ = crate::leanh::lean_box(0);
                        v_isShared_2188_ = v_isSharedCheck_2192_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2188_ == 0 {
                    v___x_2190_ = v___x_2187_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
                    v___x_2190_ = v_reuseFailAlloc_2191_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2190_;
            }
            5 => {
                v___x_2200_ = (crate::leanh::lean_unbox(v_a_2196_) as u8);
                crate::leanh::lean_dec(v_a_2196_);
                if v___x_2200_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2167_);
                    crate::leanh::lean_dec_ref(v_arg_2166_);
                    crate::leanh::lean_dec_ref(v_arg_2163_);
                    crate::leanh::lean_dec_ref(v_arg_2160_);
                    crate::leanh::lean_dec_ref(v_e_2143_);
                    v___x_2201_ = crate::leanh::lean_box(0);
                    if v_isShared_2199_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2198_, 0, v___x_2201_);
                        v___x_2203_ = v___x_2198_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
                        v___x_2203_ = v_reuseFailAlloc_2204_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2198_);
                    crate::leanh::lean_inc_ref(v_arg_2160_);
                    v___x_2205_ = l_Lean_Expr_eta(v_arg_2160_);
                    v___x_2206_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_2160_,
                            v___x_2205_,
                        );
                    if v___x_2206_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_2160_);
                        v___x_2207_ = l_Lean_Meta_Grind_preprocessLight___redArg(
                            v___x_2205_,
                            v_a_2145_,
                            v_a_2146_,
                            v_a_2147_,
                            v_a_2148_,
                            v_a_2149_,
                            v_a_2150_,
                            v_a_2151_,
                            v_a_2152_,
                            v_a_2153_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2207_) == 0 {
                            v_a_2208_ = crate::leanh::lean_ctor_get(v___x_2207_, 0);
                            crate::leanh::lean_inc(v_a_2208_);
                            crate::leanh::lean_dec_ref_known(v___x_2207_, 1);
                            v___x_2209_ =
                                l_Lean_Meta_Grind_getGeneration___redArg(v_e_2143_, v_a_2144_);
                            if crate::leanh::lean_obj_tag(v___x_2209_) == 0 {
                                v_a_2210_ = crate::leanh::lean_ctor_get(v___x_2209_, 0);
                                crate::leanh::lean_inc(v_a_2210_);
                                crate::leanh::lean_dec_ref_known(v___x_2209_, 1);
                                v___x_2211_ = crate::leanh::lean_box(0);
                                crate::leanh::lean_inc(v_a_2153_);
                                crate::leanh::lean_inc_ref(v_a_2152_);
                                crate::leanh::lean_inc(v_a_2151_);
                                crate::leanh::lean_inc_ref(v_a_2150_);
                                crate::leanh::lean_inc(v_a_2149_);
                                crate::leanh::lean_inc_ref(v_a_2148_);
                                crate::leanh::lean_inc(v_a_2147_);
                                crate::leanh::lean_inc_ref(v_a_2146_);
                                crate::leanh::lean_inc(v_a_2145_);
                                crate::leanh::lean_inc(v_a_2144_);
                                crate::leanh::lean_inc(v_a_2208_);
                                v___x_2212_ = lean_grind_internalize(
                                    v_a_2208_,
                                    v_a_2210_,
                                    v___x_2211_,
                                    v_a_2144_,
                                    v_a_2145_,
                                    v_a_2146_,
                                    v_a_2147_,
                                    v_a_2148_,
                                    v_a_2149_,
                                    v_a_2150_,
                                    v_a_2151_,
                                    v_a_2152_,
                                    v_a_2153_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2212_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2212_, 1);
                                    v_f_2169_ = v_a_2208_;
                                    v___y_2170_ = v_a_2144_;
                                    v___y_2171_ = v_a_2145_;
                                    v___y_2172_ = v_a_2146_;
                                    v___y_2173_ = v_a_2147_;
                                    v___y_2174_ = v_a_2148_;
                                    v___y_2175_ = v_a_2149_;
                                    v___y_2176_ = v_a_2150_;
                                    v___y_2177_ = v_a_2151_;
                                    v___y_2178_ = v_a_2152_;
                                    v___y_2179_ = v_a_2153_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_2208_);
                                    crate::leanh::lean_dec_ref(v___x_2167_);
                                    crate::leanh::lean_dec_ref(v_arg_2166_);
                                    crate::leanh::lean_dec_ref(v_arg_2163_);
                                    crate::leanh::lean_dec_ref(v_e_2143_);
                                    return v___x_2212_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2208_);
                                crate::leanh::lean_dec_ref(v___x_2167_);
                                crate::leanh::lean_dec_ref(v_arg_2166_);
                                crate::leanh::lean_dec_ref(v_arg_2163_);
                                crate::leanh::lean_dec_ref(v_e_2143_);
                                v_a_2213_ = crate::leanh::lean_ctor_get(v___x_2209_, 0);
                                v_isSharedCheck_2220_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2209_)) as u8;
                                if v_isSharedCheck_2220_ == 0 {
                                    v___x_2215_ = v___x_2209_;
                                    v_isShared_2216_ = v_isSharedCheck_2220_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2213_);
                                    crate::leanh::lean_dec(v___x_2209_);
                                    v___x_2215_ = crate::leanh::lean_box(0);
                                    v_isShared_2216_ = v_isSharedCheck_2220_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2167_);
                            crate::leanh::lean_dec_ref(v_arg_2166_);
                            crate::leanh::lean_dec_ref(v_arg_2163_);
                            crate::leanh::lean_dec_ref(v_e_2143_);
                            v_a_2221_ = crate::leanh::lean_ctor_get(v___x_2207_, 0);
                            v_isSharedCheck_2228_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2207_)) as u8;
                            if v_isSharedCheck_2228_ == 0 {
                                v___x_2223_ = v___x_2207_;
                                v_isShared_2224_ = v_isSharedCheck_2228_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2221_);
                                crate::leanh::lean_dec(v___x_2207_);
                                v___x_2223_ = crate::leanh::lean_box(0);
                                v_isShared_2224_ = v_isSharedCheck_2228_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2205_);
                        v_f_2169_ = v_arg_2160_;
                        v___y_2170_ = v_a_2144_;
                        v___y_2171_ = v_a_2145_;
                        v___y_2172_ = v_a_2146_;
                        v___y_2173_ = v_a_2147_;
                        v___y_2174_ = v_a_2148_;
                        v___y_2175_ = v_a_2149_;
                        v___y_2176_ = v_a_2150_;
                        v___y_2177_ = v_a_2151_;
                        v___y_2178_ = v_a_2152_;
                        v___y_2179_ = v_a_2153_;
                        state = 2;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2203_;
            }
            7 => {
                if v_isShared_2216_ == 0 {
                    v___x_2218_ = v___x_2215_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
                    v___x_2218_ = v_reuseFailAlloc_2219_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2218_;
            }
            9 => {
                if v_isShared_2224_ == 0 {
                    v___x_2226_ = v___x_2223_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
                    v___x_2226_ = v_reuseFailAlloc_2227_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2226_;
            }
            11 => {
                if v_isShared_2233_ == 0 {
                    v___x_2235_ = v___x_2232_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
                    v___x_2235_ = v_reuseFailAlloc_2236_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed(
    mut v_e_2238_: *mut crate::leanh::LeanObject,
    mut v_a_2239_: *mut crate::leanh::LeanObject,
    mut v_a_2240_: *mut crate::leanh::LeanObject,
    mut v_a_2241_: *mut crate::leanh::LeanObject,
    mut v_a_2242_: *mut crate::leanh::LeanObject,
    mut v_a_2243_: *mut crate::leanh::LeanObject,
    mut v_a_2244_: *mut crate::leanh::LeanObject,
    mut v_a_2245_: *mut crate::leanh::LeanObject,
    mut v_a_2246_: *mut crate::leanh::LeanObject,
    mut v_a_2247_: *mut crate::leanh::LeanObject,
    mut v_a_2248_: *mut crate::leanh::LeanObject,
    mut v_a_2249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2250_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(
        v_e_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_,
        v_a_2246_, v_a_2247_, v_a_2248_,
    );
    crate::leanh::lean_dec(v_a_2248_);
    crate::leanh::lean_dec_ref(v_a_2247_);
    crate::leanh::lean_dec(v_a_2246_);
    crate::leanh::lean_dec_ref(v_a_2245_);
    crate::leanh::lean_dec(v_a_2244_);
    crate::leanh::lean_dec_ref(v_a_2243_);
    crate::leanh::lean_dec(v_a_2242_);
    crate::leanh::lean_dec_ref(v_a_2241_);
    crate::leanh::lean_dec(v_a_2240_);
    crate::leanh::lean_dec(v_a_2239_);
    return v_res_2250_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ =
        l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2;
    v___x_2253_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed
            as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_2254_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2252_, v___x_2253_);
    return v___x_2254_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8____boxed(
    mut v_a_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_();
    return v_res_2256_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj(
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
    res = runtime_initialize_Init_Grind_Propagator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_PropagateInj(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_PropagateInj(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_Grind_Propagator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
}
