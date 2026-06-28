// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.PropagateInj
// Imports: Lean.Meta.Tactic.Grind.Types Init.Grind.Propagator Init.Grind.Injective Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Simp
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Grind::Injective::{
    initialize_Init_Grind_Injective, runtime_initialize_Init_Grind_Injective,
};
use crate::r#gen::Init::Grind::Propagator::{
    initialize_Init_Grind_Propagator, runtime_initialize_Init_Grind_Propagator,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
    lean_nat_sub, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_internalize;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_11, lean_box,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 73, 110, 106, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1_value: LeanStringObject<74> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 80, 114, 111, 112, 97, 103, 97, 116, 101, 73, 110, 106, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 103, 101, 116, 73, 110, 118, 70, 111, 114, 63, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [78, 111, 110, 101, 109, 112, 116, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 110, 116, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__4_value) as *mut LeanObject,13229434762204987278 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__5_value) as *mut LeanObject,7945323172821520753 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [108, 101, 102, 116, 73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__9_value) as *mut LeanObject,4547445378961686909 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [108, 101, 102, 116, 73, 110, 118, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__7_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__8_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__12_value) as *mut LeanObject,11626608933517746935 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkInjEq___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkInjEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkInjEq___closed__1_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkInjEq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkInjEq___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkInjEq___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__0_value) as *mut LeanObject,
        15947788021050471391 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__1_value) as *mut LeanObject,
        1891887995088964530 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkInjEq___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__3_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__2_value) as *mut LeanObject,
        16986677381411493332 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkInjEq___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkInjEq___closed__4_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkInjEq___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_mkInjEq___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__4_value) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_mkInjEq___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__5_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkInjEq___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkInjEq___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkInjEq___closed__7_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_mkInjEq___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkInjEq___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_mkInjEq___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_mkInjEq___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [70, 117, 110, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 106, 101, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__0_value) as *mut LeanObject,920240211420121313 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__1_value) as *mut LeanObject,14487767036850709044 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2_value) as *mut LeanObject;
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    v___x_1129_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_1129_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(
    mut v_msg_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
    mut v___y_1134_: *mut LeanObject,
    mut v___y_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
    mut v___y_1138_: *mut LeanObject,
    mut v___y_1139_: *mut LeanObject,
    mut v___y_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9023__overap_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    v___x_1142_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___closed__0);
    v___x_9023__overap_1143_ = lean_panic_fn_borrowed(v___x_1142_, v_msg_1130_);
    lean_inc(v___y_1140_);
    lean_inc_ref(v___y_1139_);
    lean_inc(v___y_1138_);
    lean_inc_ref(v___y_1137_);
    lean_inc(v___y_1136_);
    lean_inc_ref(v___y_1135_);
    lean_inc(v___y_1134_);
    lean_inc_ref(v___y_1133_);
    lean_inc(v___y_1132_);
    lean_inc(v___y_1131_);
    v___x_1144_ = lean_apply_11(
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
        lean_box(0),
    );
    return v___x_1144_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0___boxed(
    mut v_msg_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
    mut v___y_1148_: *mut LeanObject,
    mut v___y_1149_: *mut LeanObject,
    mut v___y_1150_: *mut LeanObject,
    mut v___y_1151_: *mut LeanObject,
    mut v___y_1152_: *mut LeanObject,
    mut v___y_1153_: *mut LeanObject,
    mut v___y_1154_: *mut LeanObject,
    mut v___y_1155_: *mut LeanObject,
    mut v___y_1156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1157_: *mut LeanObject = core::ptr::null_mut();
    v_res_1157_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v_msg_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
    lean_dec(v___y_1155_);
    lean_dec_ref(v___y_1154_);
    lean_dec(v___y_1153_);
    lean_dec_ref(v___y_1152_);
    lean_dec(v___y_1151_);
    lean_dec_ref(v___y_1150_);
    lean_dec(v___y_1149_);
    lean_dec_ref(v___y_1148_);
    lean_dec(v___y_1147_);
    lean_dec(v___y_1146_);
    return v_res_1157_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(
    mut v_keys_1158_: *mut LeanObject,
    mut v_vals_1159_: *mut LeanObject,
    mut v_i_1160_: *mut LeanObject,
    mut v_k_1161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1162_ = lean_array_get_size(v_keys_1158_);
                v___x_1163_ = lean_nat_dec_lt(v_i_1160_, v___x_1162_);
                if v___x_1163_ == 0 {
                    lean_dec(v_i_1160_);
                    v___x_1164_ = lean_box(0);
                    return v___x_1164_;
                } else {
                    v_k_x27_1165_ = lean_array_fget_borrowed(v_keys_1158_, v_i_1160_);
                    v___x_1166_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1161_,
                            v_k_x27_1165_,
                        );
                    if v___x_1166_ == 0 {
                        v___x_1167_ = lean_unsigned_to_nat(1);
                        v___x_1168_ = lean_nat_add(v_i_1160_, v___x_1167_);
                        lean_dec(v_i_1160_);
                        v_i_1160_ = v___x_1168_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1170_ = lean_array_fget_borrowed(v_vals_1159_, v_i_1160_);
                        lean_dec(v_i_1160_);
                        lean_inc(v___x_1170_);
                        v___x_1171_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1171_, 0, v___x_1170_);
                        return v___x_1171_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_keys_1172_: *mut LeanObject,
    mut v_vals_1173_: *mut LeanObject,
    mut v_i_1174_: *mut LeanObject,
    mut v_k_1175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1176_: *mut LeanObject = core::ptr::null_mut();
    v_res_1176_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_1172_, v_vals_1173_, v_i_1174_, v_k_1175_);
    lean_dec_ref(v_k_1175_);
    lean_dec_ref(v_vals_1173_);
    lean_dec_ref(v_keys_1172_);
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
    v___x_1181_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__0);
    v___x_1182_ = lean_usize_sub(v___x_1181_, v___x_1180_);
    return v___x_1182_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(
    mut v_x_1183_: *mut LeanObject,
    mut v_x_1184_: usize,
    mut v_x_1185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: usize = 0;
    let mut v___x_1189_: usize = 0;
    let mut v___x_1190_: usize = 0;
    let mut v_j_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: u8 = 0;
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: usize = 0;
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1183_) == 0 {
                    v_es_1186_ = lean_ctor_get(v_x_1183_, 0);
                    v___x_1187_ = lean_box(2);
                    v___x_1188_ = 5usize;
                    v___x_1189_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
                    v___x_1190_ = lean_usize_land(v_x_1184_, v___x_1189_);
                    v_j_1191_ = lean_usize_to_nat(v___x_1190_);
                    v___x_1192_ = lean_array_get_borrowed(v___x_1187_, v_es_1186_, v_j_1191_);
                    lean_dec(v_j_1191_);
                    match lean_obj_tag(v___x_1192_) {
                        0 => {
                            v_key_1193_ = lean_ctor_get(v___x_1192_, 0);
                            v_val_1194_ = lean_ctor_get(v___x_1192_, 1);
                            v___x_1195_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1185_, v_key_1193_);
                            if v___x_1195_ == 0 {
                                v___x_1196_ = lean_box(0);
                                return v___x_1196_;
                            } else {
                                lean_inc(v_val_1194_);
                                v___x_1197_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1197_, 0, v_val_1194_);
                                return v___x_1197_;
                            }
                        }
                        1 => {
                            v_node_1198_ = lean_ctor_get(v___x_1192_, 0);
                            v___x_1199_ = lean_usize_shift_right(v_x_1184_, v___x_1188_);
                            v_x_1183_ = v_node_1198_;
                            v_x_1184_ = v___x_1199_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1201_ = lean_box(0);
                            return v___x_1201_;
                        }
                    }
                } else {
                    v_ks_1202_ = lean_ctor_get(v_x_1183_, 0);
                    v_vs_1203_ = lean_ctor_get(v_x_1183_, 1);
                    v___x_1204_ = lean_unsigned_to_nat(0);
                    v___x_1205_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_ks_1202_, v_vs_1203_, v___x_1204_, v_x_1185_);
                    return v___x_1205_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___boxed(
    mut v_x_1206_: *mut LeanObject,
    mut v_x_1207_: *mut LeanObject,
    mut v_x_1208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9505__boxed_1209_: usize = 0;
    let mut v_res_1210_: *mut LeanObject = core::ptr::null_mut();
    v_x_9505__boxed_1209_ = lean_unbox_usize(v_x_1207_);
    lean_dec(v_x_1207_);
    v_res_1210_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_1206_, v_x_9505__boxed_1209_, v_x_1208_);
    lean_dec_ref(v_x_1208_);
    lean_dec_ref(v_x_1206_);
    return v_res_1210_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(
    mut v_x_1211_: *mut LeanObject,
    mut v_x_1212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1213_: u64 = 0;
    let mut v___x_1214_: usize = 0;
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    v___x_1213_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1212_);
    v___x_1214_ = lean_uint64_to_usize(v___x_1213_);
    v___x_1215_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_1211_, v___x_1214_, v_x_1212_);
    return v___x_1215_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg___boxed(
    mut v_x_1216_: *mut LeanObject,
    mut v_x_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1218_: *mut LeanObject = core::ptr::null_mut();
    v_res_1218_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_1216_, v_x_1217_);
    lean_dec_ref(v_x_1217_);
    lean_dec_ref(v_x_1216_);
    return v_res_1218_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(
    mut v_x_1219_: *mut LeanObject,
    mut v_x_1220_: *mut LeanObject,
    mut v_x_1221_: *mut LeanObject,
    mut v_x_1222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1227_: u8 = 0;
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: u8 = 0;
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1223_ = lean_ctor_get(v_x_1219_, 0);
                v_vs_1224_ = lean_ctor_get(v_x_1219_, 1);
                v_isSharedCheck_1248_ = (!lean_is_exclusive(v_x_1219_)) as u8;
                if v_isSharedCheck_1248_ == 0 {
                    v___x_1226_ = v_x_1219_;
                    v_isShared_1227_ = v_isSharedCheck_1248_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1224_);
                    lean_inc(v_ks_1223_);
                    lean_dec(v_x_1219_);
                    v___x_1226_ = lean_box(0);
                    v_isShared_1227_ = v_isSharedCheck_1248_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1228_ = lean_array_get_size(v_ks_1223_);
                v___x_1229_ = lean_nat_dec_lt(v_x_1220_, v___x_1228_);
                if v___x_1229_ == 0 {
                    lean_dec(v_x_1220_);
                    v___x_1230_ = lean_array_push(v_ks_1223_, v_x_1221_);
                    v___x_1231_ = lean_array_push(v_vs_1224_, v_x_1222_);
                    if v_isShared_1227_ == 0 {
                        lean_ctor_set(v___x_1226_, 1, v___x_1231_);
                        lean_ctor_set(v___x_1226_, 0, v___x_1230_);
                        v___x_1233_ = v___x_1226_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1230_);
                        lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1231_);
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
                            v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_ks_1223_);
                            lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_vs_1224_);
                            v___x_1238_ = v_reuseFailAlloc_1242_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1243_ = lean_array_fset(v_ks_1223_, v_x_1220_, v_x_1221_);
                        v___x_1244_ = lean_array_fset(v_vs_1224_, v_x_1220_, v_x_1222_);
                        lean_dec(v_x_1220_);
                        if v_isShared_1227_ == 0 {
                            lean_ctor_set(v___x_1226_, 1, v___x_1244_);
                            lean_ctor_set(v___x_1226_, 0, v___x_1243_);
                            v___x_1246_ = v___x_1226_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1243_);
                            lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1244_);
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
                v___x_1239_ = lean_unsigned_to_nat(1);
                v___x_1240_ = lean_nat_add(v_x_1220_, v___x_1239_);
                lean_dec(v_x_1220_);
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
    mut v_n_1249_: *mut LeanObject,
    mut v_k_1250_: *mut LeanObject,
    mut v_v_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    v___x_1252_ = lean_unsigned_to_nat(0);
    v___x_1253_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_n_1249_, v___x_1252_, v_k_1250_, v_v_1251_);
    return v___x_1253_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    v___x_1254_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1254_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(
    mut v_x_1255_: *mut LeanObject,
    mut v_x_1256_: usize,
    mut v_x_1257_: usize,
    mut v_x_1258_: *mut LeanObject,
    mut v_x_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: usize = 0;
    let mut v___x_1262_: usize = 0;
    let mut v___x_1263_: usize = 0;
    let mut v___x_1264_: usize = 0;
    let mut v_j_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: u8 = 0;
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1270_: u8 = 0;
    let mut v_v_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1284_: u8 = 0;
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1291_: u8 = 0;
    let mut v_node_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1295_: u8 = 0;
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: usize = 0;
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1302_: u8 = 0;
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1304_: u8 = 0;
    let mut v_unused_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1310_: u8 = 0;
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1315_: u8 = 0;
    let mut v_ks_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: usize = 0;
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: u8 = 0;
    let mut v_reuseFailAlloc_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1327_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1255_) == 0 {
                    v_es_1260_ = lean_ctor_get(v_x_1255_, 0);
                    v___x_1261_ = 5usize;
                    v___x_1262_ = 1usize;
                    v___x_1263_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
                    v___x_1264_ = lean_usize_land(v_x_1256_, v___x_1263_);
                    v_j_1265_ = lean_usize_to_nat(v___x_1264_);
                    v___x_1266_ = lean_array_get_size(v_es_1260_);
                    v___x_1267_ = lean_nat_dec_lt(v_j_1265_, v___x_1266_);
                    if v___x_1267_ == 0 {
                        lean_dec(v_j_1265_);
                        lean_dec(v_x_1259_);
                        lean_dec_ref(v_x_1258_);
                        return v_x_1255_;
                    } else {
                        lean_inc_ref(v_es_1260_);
                        v_isSharedCheck_1304_ = (!lean_is_exclusive(v_x_1255_)) as u8;
                        if v_isSharedCheck_1304_ == 0 {
                            v_unused_1305_ = lean_ctor_get(v_x_1255_, 0);
                            lean_dec(v_unused_1305_);
                            v___x_1269_ = v_x_1255_;
                            v_isShared_1270_ = v_isSharedCheck_1304_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1255_);
                            v___x_1269_ = lean_box(0);
                            v_isShared_1270_ = v_isSharedCheck_1304_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1306_ = lean_ctor_get(v_x_1255_, 0);
                    v_vs_1307_ = lean_ctor_get(v_x_1255_, 1);
                    v_isSharedCheck_1327_ = (!lean_is_exclusive(v_x_1255_)) as u8;
                    if v_isSharedCheck_1327_ == 0 {
                        v___x_1309_ = v_x_1255_;
                        v_isShared_1310_ = v_isSharedCheck_1327_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1307_);
                        lean_inc(v_ks_1306_);
                        lean_dec(v_x_1255_);
                        v___x_1309_ = lean_box(0);
                        v_isShared_1310_ = v_isSharedCheck_1327_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1271_ = lean_array_fget(v_es_1260_, v_j_1265_);
                v___x_1272_ = lean_box(0);
                v_xs_x27_1273_ = lean_array_fset(v_es_1260_, v_j_1265_, v___x_1272_);
                match lean_obj_tag(v_v_1271_) {
                    0 => {
                        v_key_1280_ = lean_ctor_get(v_v_1271_, 0);
                        v_val_1281_ = lean_ctor_get(v_v_1271_, 1);
                        v_isSharedCheck_1291_ = (!lean_is_exclusive(v_v_1271_)) as u8;
                        if v_isSharedCheck_1291_ == 0 {
                            v___x_1283_ = v_v_1271_;
                            v_isShared_1284_ = v_isSharedCheck_1291_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1281_);
                            lean_inc(v_key_1280_);
                            lean_dec(v_v_1271_);
                            v___x_1283_ = lean_box(0);
                            v_isShared_1284_ = v_isSharedCheck_1291_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1292_ = lean_ctor_get(v_v_1271_, 0);
                        v_isSharedCheck_1302_ = (!lean_is_exclusive(v_v_1271_)) as u8;
                        if v_isSharedCheck_1302_ == 0 {
                            v___x_1294_ = v_v_1271_;
                            v_isShared_1295_ = v_isSharedCheck_1302_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1292_);
                            lean_dec(v_v_1271_);
                            v___x_1294_ = lean_box(0);
                            v_isShared_1295_ = v_isSharedCheck_1302_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1303_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1303_, 0, v_x_1258_);
                        lean_ctor_set(v___x_1303_, 1, v_x_1259_);
                        v___y_1275_ = v___x_1303_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1276_ = lean_array_fset(v_xs_x27_1273_, v_j_1265_, v___y_1275_);
                lean_dec(v_j_1265_);
                if v_isShared_1270_ == 0 {
                    lean_ctor_set(v___x_1269_, 0, v___x_1276_);
                    v___x_1278_ = v___x_1269_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
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
                    lean_del_object(v___x_1283_);
                    v___x_1286_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1280_,
                        v_val_1281_,
                        v_x_1258_,
                        v_x_1259_,
                    );
                    v___x_1287_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1287_, 0, v___x_1286_);
                    v___y_1275_ = v___x_1287_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1281_);
                    lean_dec(v_key_1280_);
                    if v_isShared_1284_ == 0 {
                        lean_ctor_set(v___x_1283_, 1, v_x_1259_);
                        lean_ctor_set(v___x_1283_, 0, v_x_1258_);
                        v___x_1289_ = v___x_1283_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_x_1258_);
                        lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_x_1259_);
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
                    lean_ctor_set(v___x_1294_, 0, v___x_1298_);
                    v___x_1300_ = v___x_1294_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
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
                    v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_ks_1306_);
                    lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_vs_1307_);
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
                    v___x_1324_ = lean_unsigned_to_nat(4);
                    v___x_1325_ = lean_nat_dec_lt(v___x_1323_, v___x_1324_);
                    lean_dec(v___x_1323_);
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
                    v_ks_1316_ = lean_ctor_get(v_newNode_1313_, 0);
                    lean_inc_ref(v_ks_1316_);
                    v_vs_1317_ = lean_ctor_get(v_newNode_1313_, 1);
                    lean_inc_ref(v_vs_1317_);
                    lean_dec_ref(v_newNode_1313_);
                    v___x_1318_ = lean_unsigned_to_nat(0);
                    v___x_1319_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___closed__0);
                    v___x_1320_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_x_1257_, v_ks_1316_, v_vs_1317_, v___x_1318_, v___x_1319_);
                    lean_dec_ref(v_vs_1317_);
                    lean_dec_ref(v_ks_1316_);
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
    mut v_keys_1329_: *mut LeanObject,
    mut v_vals_1330_: *mut LeanObject,
    mut v_i_1331_: *mut LeanObject,
    mut v_entries_1332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: u8 = 0;
    let mut v_k_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u64 = 0;
    let mut v_h_1338_: usize = 0;
    let mut v___x_1339_: usize = 0;
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: usize = 0;
    let mut v___x_1342_: usize = 0;
    let mut v___x_1343_: usize = 0;
    let mut v_h_1344_: usize = 0;
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1333_ = lean_array_get_size(v_keys_1329_);
                v___x_1334_ = lean_nat_dec_lt(v_i_1331_, v___x_1333_);
                if v___x_1334_ == 0 {
                    lean_dec(v_i_1331_);
                    return v_entries_1332_;
                } else {
                    v_k_1335_ = lean_array_fget_borrowed(v_keys_1329_, v_i_1331_);
                    v_v_1336_ = lean_array_fget_borrowed(v_vals_1330_, v_i_1331_);
                    v___x_1337_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1335_);
                    v_h_1338_ = lean_uint64_to_usize(v___x_1337_);
                    v___x_1339_ = 5usize;
                    v___x_1340_ = lean_unsigned_to_nat(1);
                    v___x_1341_ = 1usize;
                    v___x_1342_ = lean_usize_sub(v_depth_1328_, v___x_1341_);
                    v___x_1343_ = lean_usize_mul(v___x_1339_, v___x_1342_);
                    v_h_1344_ = lean_usize_shift_right(v_h_1338_, v___x_1343_);
                    v___x_1345_ = lean_nat_add(v_i_1331_, v___x_1340_);
                    lean_dec(v_i_1331_);
                    lean_inc(v_v_1336_);
                    lean_inc(v_k_1335_);
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
    mut v_depth_1348_: *mut LeanObject,
    mut v_keys_1349_: *mut LeanObject,
    mut v_vals_1350_: *mut LeanObject,
    mut v_i_1351_: *mut LeanObject,
    mut v_entries_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1353_: usize = 0;
    let mut v_res_1354_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1353_ = lean_unbox_usize(v_depth_1348_);
    lean_dec(v_depth_1348_);
    v_res_1354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_boxed_1353_, v_keys_1349_, v_vals_1350_, v_i_1351_, v_entries_1352_);
    lean_dec_ref(v_vals_1350_);
    lean_dec_ref(v_keys_1349_);
    return v_res_1354_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg___boxed(
    mut v_x_1355_: *mut LeanObject,
    mut v_x_1356_: *mut LeanObject,
    mut v_x_1357_: *mut LeanObject,
    mut v_x_1358_: *mut LeanObject,
    mut v_x_1359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9652__boxed_1360_: usize = 0;
    let mut v_x_9653__boxed_1361_: usize = 0;
    let mut v_res_1362_: *mut LeanObject = core::ptr::null_mut();
    v_x_9652__boxed_1360_ = lean_unbox_usize(v_x_1356_);
    lean_dec(v_x_1356_);
    v_x_9653__boxed_1361_ = lean_unbox_usize(v_x_1357_);
    lean_dec(v_x_1357_);
    v_res_1362_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_1355_, v_x_9652__boxed_1360_, v_x_9653__boxed_1361_, v_x_1358_, v_x_1359_);
    return v_res_1362_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(
    mut v_x_1363_: *mut LeanObject,
    mut v_x_1364_: *mut LeanObject,
    mut v_x_1365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1366_: u64 = 0;
    let mut v___x_1367_: usize = 0;
    let mut v___x_1368_: usize = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1364_);
    v___x_1367_ = lean_uint64_to_usize(v___x_1366_);
    v___x_1368_ = 1usize;
    v___x_1369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_1363_, v___x_1367_, v___x_1368_, v_x_1364_, v_x_1365_);
    return v___x_1369_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3()
-> *mut LeanObject {
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    v___x_1373_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__2;
    v___x_1374_ = lean_unsigned_to_nat(26);
    v___x_1375_ = lean_unsigned_to_nat(19);
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
-> *mut LeanObject {
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1392_: *mut LeanObject = core::ptr::null_mut();
    v___x_1391_ = lean_box(0);
    v_dummy_1392_ = l_Lean_Expr_sort___override(v___x_1391_);
    return v_dummy_1392_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(
    mut v_f_1398_: *mut LeanObject,
    mut v_a_1399_: *mut LeanObject,
    mut v_a_1400_: *mut LeanObject,
    mut v_a_1401_: *mut LeanObject,
    mut v_a_1402_: *mut LeanObject,
    mut v_a_1403_: *mut LeanObject,
    mut v_a_1404_: *mut LeanObject,
    mut v_a_1405_: *mut LeanObject,
    mut v_a_1406_: *mut LeanObject,
    mut v_a_1407_: *mut LeanObject,
    mut v_a_1408_: *mut LeanObject,
    mut v_a_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inj_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fns_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v_inv_x3f_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1443_: u8 = 0;
    let mut v_00_u03b1_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03b2_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1449_: u8 = 0;
    let mut v_head_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1463_: u8 = 0;
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inj_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1471_: u8 = 0;
    let mut v_nextDeclIdx_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprs_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parents_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrTable_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_appMap_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newFacts_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_1480_: u8 = 0;
    let mut v_nextIdx_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facts_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extThms_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematch_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_split_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_clean_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sstates_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1491_: u8 = 0;
    let mut v_thms_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fns_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1496_: u8 = 0;
    let mut v_dummy_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut v_isSharedCheck_1529_: u8 = 0;
    let mut v_unused_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v_unused_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_a_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1537_: u8 = 0;
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v_reuseFailAlloc_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1543_: u8 = 0;
    let mut v_unused_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v_unused_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1548_: u8 = 0;
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1551_: u8 = 0;
    let mut v_unused_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1424_ = lean_st_ref_get(v_a_1400_);
                v_toGoalState_1425_ = lean_ctor_get(v___x_1424_, 0);
                lean_inc_ref(v_toGoalState_1425_);
                lean_dec(v___x_1424_);
                v_inj_1426_ = lean_ctor_get(v_toGoalState_1425_, 13);
                lean_inc_ref(v_inj_1426_);
                lean_dec_ref(v_toGoalState_1425_);
                v_fns_1427_ = lean_ctor_get(v_inj_1426_, 1);
                v_isSharedCheck_1551_ = (!lean_is_exclusive(v_inj_1426_)) as u8;
                if v_isSharedCheck_1551_ == 0 {
                    v_unused_1552_ = lean_ctor_get(v_inj_1426_, 0);
                    lean_dec(v_unused_1552_);
                    v___x_1429_ = v_inj_1426_;
                    v_isShared_1430_ = v_isSharedCheck_1551_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fns_1427_);
                    lean_dec(v_inj_1426_);
                    v___x_1429_ = lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1551_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1422_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__3);
                v___x_1423_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__0(v___x_1422_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
                return v___x_1423_;
            }
            2 => {
                v___x_1431_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_fns_1427_, v_f_1398_);
                lean_dec_ref(v_fns_1427_);
                if lean_obj_tag(v___x_1431_) == 1 {
                    v_val_1432_ = lean_ctor_get(v___x_1431_, 0);
                    v_isSharedCheck_1548_ = (!lean_is_exclusive(v___x_1431_)) as u8;
                    if v_isSharedCheck_1548_ == 0 {
                        v___x_1434_ = v___x_1431_;
                        v_isShared_1435_ = v_isSharedCheck_1548_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1432_);
                        lean_dec(v___x_1431_);
                        v___x_1434_ = lean_box(0);
                        v_isShared_1435_ = v_isSharedCheck_1548_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1431_);
                    lean_del_object(v___x_1429_);
                    lean_dec_ref(v_a_1399_);
                    lean_dec_ref(v_f_1398_);
                    v___x_1549_ = lean_box(0);
                    v___x_1550_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1550_, 0, v___x_1549_);
                    return v___x_1550_;
                }
            }
            3 => {
                v_inv_x3f_1436_ = lean_ctor_get(v_val_1432_, 4);
                if lean_obj_tag(v_inv_x3f_1436_) == 1 {
                    lean_inc_ref(v_inv_x3f_1436_);
                    lean_del_object(v___x_1434_);
                    lean_dec(v_val_1432_);
                    lean_del_object(v___x_1429_);
                    lean_dec_ref(v_a_1399_);
                    lean_dec_ref(v_f_1398_);
                    v___x_1437_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1437_, 0, v_inv_x3f_1436_);
                    return v___x_1437_;
                } else {
                    v_us_1438_ = lean_ctor_get(v_val_1432_, 0);
                    lean_inc(v_us_1438_);
                    if lean_obj_tag(v_us_1438_) == 1 {
                        v_tail_1439_ = lean_ctor_get(v_us_1438_, 1);
                        lean_inc(v_tail_1439_);
                        if lean_obj_tag(v_tail_1439_) == 1 {
                            v_tail_1440_ = lean_ctor_get(v_tail_1439_, 1);
                            v_isSharedCheck_1546_ = (!lean_is_exclusive(v_tail_1439_)) as u8;
                            if v_isSharedCheck_1546_ == 0 {
                                v_unused_1547_ = lean_ctor_get(v_tail_1439_, 0);
                                lean_dec(v_unused_1547_);
                                v___x_1442_ = v_tail_1439_;
                                v_isShared_1443_ = v_isSharedCheck_1546_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_tail_1440_);
                                lean_dec(v_tail_1439_);
                                v___x_1442_ = lean_box(0);
                                v_isShared_1443_ = v_isSharedCheck_1546_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_tail_1439_);
                            lean_dec_ref_known(v_us_1438_, 2);
                            lean_del_object(v___x_1434_);
                            lean_dec(v_val_1432_);
                            lean_del_object(v___x_1429_);
                            lean_dec_ref(v_a_1399_);
                            lean_dec_ref(v_f_1398_);
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
                        lean_dec(v_us_1438_);
                        lean_del_object(v___x_1434_);
                        lean_dec(v_val_1432_);
                        lean_del_object(v___x_1429_);
                        lean_dec_ref(v_a_1399_);
                        lean_dec_ref(v_f_1398_);
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
                if lean_obj_tag(v_tail_1440_) == 0 {
                    v_00_u03b1_1444_ = lean_ctor_get(v_val_1432_, 1);
                    v_00_u03b2_1445_ = lean_ctor_get(v_val_1432_, 2);
                    v_h_1446_ = lean_ctor_get(v_val_1432_, 3);
                    v_isSharedCheck_1543_ = (!lean_is_exclusive(v_val_1432_)) as u8;
                    if v_isSharedCheck_1543_ == 0 {
                        v_unused_1544_ = lean_ctor_get(v_val_1432_, 4);
                        lean_dec(v_unused_1544_);
                        v_unused_1545_ = lean_ctor_get(v_val_1432_, 0);
                        lean_dec(v_unused_1545_);
                        v___x_1448_ = v_val_1432_;
                        v_isShared_1449_ = v_isSharedCheck_1543_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_h_1446_);
                        lean_inc(v_00_u03b2_1445_);
                        lean_inc(v_00_u03b1_1444_);
                        lean_dec(v_val_1432_);
                        v___x_1448_ = lean_box(0);
                        v_isShared_1449_ = v_isSharedCheck_1543_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1442_);
                    lean_dec(v_tail_1440_);
                    lean_dec_ref_known(v_us_1438_, 2);
                    lean_del_object(v___x_1434_);
                    lean_dec(v_val_1432_);
                    lean_del_object(v___x_1429_);
                    lean_dec_ref(v_a_1399_);
                    lean_dec_ref(v_f_1398_);
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
                v_head_1450_ = lean_ctor_get(v_us_1438_, 0);
                v___x_1451_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__6;
                lean_inc(v_head_1450_);
                if v_isShared_1443_ == 0 {
                    lean_ctor_set(v___x_1442_, 0, v_head_1450_);
                    v___x_1453_ = v___x_1442_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_head_1450_);
                    lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_tail_1440_);
                    v___x_1453_ = v_reuseFailAlloc_1542_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1454_ = l_Lean_mkConst(v___x_1451_, v___x_1453_);
                lean_inc_ref_n(v_00_u03b1_1444_, 2);
                v___x_1455_ = l_Lean_mkAppB(v___x_1454_, v_00_u03b1_1444_, v_a_1399_);
                v___x_1456_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__10;
                lean_inc_ref(v_us_1438_);
                v___x_1457_ = l_Lean_mkConst(v___x_1456_, v_us_1438_);
                lean_inc_ref(v_h_1446_);
                lean_inc_ref(v_f_1398_);
                lean_inc_ref(v_00_u03b2_1445_);
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
                if lean_obj_tag(v___x_1459_) == 0 {
                    v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
                    v_isSharedCheck_1533_ = (!lean_is_exclusive(v___x_1459_)) as u8;
                    if v_isSharedCheck_1533_ == 0 {
                        v___x_1462_ = v___x_1459_;
                        v_isShared_1463_ = v_isSharedCheck_1533_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1460_);
                        lean_dec(v___x_1459_);
                        v___x_1462_ = lean_box(0);
                        v_isShared_1463_ = v_isSharedCheck_1533_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1448_);
                    lean_dec_ref(v_h_1446_);
                    lean_dec_ref(v_00_u03b2_1445_);
                    lean_dec_ref(v_00_u03b1_1444_);
                    lean_dec_ref_known(v_us_1438_, 2);
                    lean_del_object(v___x_1434_);
                    lean_del_object(v___x_1429_);
                    lean_dec_ref(v_f_1398_);
                    v_a_1534_ = lean_ctor_get(v___x_1459_, 0);
                    v_isSharedCheck_1541_ = (!lean_is_exclusive(v___x_1459_)) as u8;
                    if v_isSharedCheck_1541_ == 0 {
                        v___x_1536_ = v___x_1459_;
                        v_isShared_1537_ = v_isSharedCheck_1541_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_1534_);
                        lean_dec(v___x_1459_);
                        v___x_1536_ = lean_box(0);
                        v_isShared_1537_ = v_isSharedCheck_1541_;
                        state = 18;
                        continue;
                    }
                }
            }
            7 => {
                v___x_1464_ = lean_st_ref_take(v_a_1400_);
                v_nargs_1465_ = l_Lean_Expr_getAppNumArgs(v_a_1460_);
                v_toGoalState_1466_ = lean_ctor_get(v___x_1464_, 0);
                lean_inc_ref(v_toGoalState_1466_);
                v_inj_1467_ = lean_ctor_get(v_toGoalState_1466_, 13);
                lean_inc_ref(v_inj_1467_);
                v_mvarId_1468_ = lean_ctor_get(v___x_1464_, 1);
                v_isSharedCheck_1531_ = (!lean_is_exclusive(v___x_1464_)) as u8;
                if v_isSharedCheck_1531_ == 0 {
                    v_unused_1532_ = lean_ctor_get(v___x_1464_, 0);
                    lean_dec(v_unused_1532_);
                    v___x_1470_ = v___x_1464_;
                    v_isShared_1471_ = v_isSharedCheck_1531_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_mvarId_1468_);
                    lean_dec(v___x_1464_);
                    v___x_1470_ = lean_box(0);
                    v_isShared_1471_ = v_isSharedCheck_1531_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_nextDeclIdx_1472_ = lean_ctor_get(v_toGoalState_1466_, 0);
                v_enodeMap_1473_ = lean_ctor_get(v_toGoalState_1466_, 1);
                v_exprs_1474_ = lean_ctor_get(v_toGoalState_1466_, 2);
                v_parents_1475_ = lean_ctor_get(v_toGoalState_1466_, 3);
                v_congrTable_1476_ = lean_ctor_get(v_toGoalState_1466_, 4);
                v_appMap_1477_ = lean_ctor_get(v_toGoalState_1466_, 5);
                v_indicesFound_1478_ = lean_ctor_get(v_toGoalState_1466_, 6);
                v_newFacts_1479_ = lean_ctor_get(v_toGoalState_1466_, 7);
                v_inconsistent_1480_ = lean_ctor_get_uint8(
                    v_toGoalState_1466_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                v_nextIdx_1481_ = lean_ctor_get(v_toGoalState_1466_, 8);
                v_newRawFacts_1482_ = lean_ctor_get(v_toGoalState_1466_, 9);
                v_facts_1483_ = lean_ctor_get(v_toGoalState_1466_, 10);
                v_extThms_1484_ = lean_ctor_get(v_toGoalState_1466_, 11);
                v_ematch_1485_ = lean_ctor_get(v_toGoalState_1466_, 12);
                v_split_1486_ = lean_ctor_get(v_toGoalState_1466_, 14);
                v_clean_1487_ = lean_ctor_get(v_toGoalState_1466_, 15);
                v_sstates_1488_ = lean_ctor_get(v_toGoalState_1466_, 16);
                v_isSharedCheck_1529_ = (!lean_is_exclusive(v_toGoalState_1466_)) as u8;
                if v_isSharedCheck_1529_ == 0 {
                    v_unused_1530_ = lean_ctor_get(v_toGoalState_1466_, 13);
                    lean_dec(v_unused_1530_);
                    v___x_1490_ = v_toGoalState_1466_;
                    v_isShared_1491_ = v_isSharedCheck_1529_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_sstates_1488_);
                    lean_inc(v_clean_1487_);
                    lean_inc(v_split_1486_);
                    lean_inc(v_ematch_1485_);
                    lean_inc(v_extThms_1484_);
                    lean_inc(v_facts_1483_);
                    lean_inc(v_newRawFacts_1482_);
                    lean_inc(v_nextIdx_1481_);
                    lean_inc(v_newFacts_1479_);
                    lean_inc(v_indicesFound_1478_);
                    lean_inc(v_appMap_1477_);
                    lean_inc(v_congrTable_1476_);
                    lean_inc(v_parents_1475_);
                    lean_inc(v_exprs_1474_);
                    lean_inc(v_enodeMap_1473_);
                    lean_inc(v_nextDeclIdx_1472_);
                    lean_dec(v_toGoalState_1466_);
                    v___x_1490_ = lean_box(0);
                    v_isShared_1491_ = v_isSharedCheck_1529_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_thms_1492_ = lean_ctor_get(v_inj_1467_, 0);
                v_fns_1493_ = lean_ctor_get(v_inj_1467_, 1);
                v_isSharedCheck_1528_ = (!lean_is_exclusive(v_inj_1467_)) as u8;
                if v_isSharedCheck_1528_ == 0 {
                    v___x_1495_ = v_inj_1467_;
                    v_isShared_1496_ = v_isSharedCheck_1528_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_fns_1493_);
                    lean_inc(v_thms_1492_);
                    lean_dec(v_inj_1467_);
                    v___x_1495_ = lean_box(0);
                    v_isShared_1496_ = v_isSharedCheck_1528_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_dummy_1497_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__11);
                lean_inc(v_nargs_1465_);
                v___x_1498_ = lean_mk_array(v_nargs_1465_, v_dummy_1497_);
                v___x_1499_ = lean_unsigned_to_nat(1);
                v___x_1500_ = lean_nat_sub(v_nargs_1465_, v___x_1499_);
                lean_dec(v_nargs_1465_);
                lean_inc(v_a_1460_);
                v___x_1501_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_a_1460_,
                    v___x_1498_,
                    v___x_1500_,
                );
                v___x_1502_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f___closed__13;
                lean_inc_ref(v_us_1438_);
                v___x_1503_ = l_Lean_mkConst(v___x_1502_, v_us_1438_);
                v___x_1504_ = l_Lean_mkAppN(v___x_1503_, v___x_1501_);
                lean_dec_ref(v___x_1501_);
                if v_isShared_1430_ == 0 {
                    lean_ctor_set(v___x_1429_, 1, v___x_1504_);
                    lean_ctor_set(v___x_1429_, 0, v_a_1460_);
                    v___x_1506_ = v___x_1429_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1460_);
                    lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1504_);
                    v___x_1506_ = v_reuseFailAlloc_1527_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1435_ == 0 {
                    lean_ctor_set(v___x_1434_, 0, v___x_1506_);
                    v___x_1508_ = v___x_1434_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1506_);
                    v___x_1508_ = v_reuseFailAlloc_1526_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                lean_inc_ref(v___x_1508_);
                if v_isShared_1449_ == 0 {
                    lean_ctor_set(v___x_1448_, 4, v___x_1508_);
                    v___x_1510_ = v___x_1448_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_us_1438_);
                    lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_00_u03b1_1444_);
                    lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_00_u03b2_1445_);
                    lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_h_1446_);
                    lean_ctor_set(v_reuseFailAlloc_1525_, 4, v___x_1508_);
                    v___x_1510_ = v_reuseFailAlloc_1525_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1511_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_1493_, v_f_1398_, v___x_1510_);
                if v_isShared_1496_ == 0 {
                    lean_ctor_set(v___x_1495_, 1, v___x_1511_);
                    v___x_1513_ = v___x_1495_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_thms_1492_);
                    lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1511_);
                    v___x_1513_ = v_reuseFailAlloc_1524_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_1491_ == 0 {
                    lean_ctor_set(v___x_1490_, 13, v___x_1513_);
                    v___x_1515_ = v___x_1490_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 17, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_nextDeclIdx_1472_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_enodeMap_1473_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_exprs_1474_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_parents_1475_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_congrTable_1476_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 5, v_appMap_1477_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 6, v_indicesFound_1478_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 7, v_newFacts_1479_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 8, v_nextIdx_1481_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 9, v_newRawFacts_1482_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 10, v_facts_1483_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 11, v_extThms_1484_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 12, v_ematch_1485_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 13, v___x_1513_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 14, v_split_1486_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 15, v_clean_1487_);
                    lean_ctor_set(v_reuseFailAlloc_1523_, 16, v_sstates_1488_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1523_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v_inconsistent_1480_,
                    );
                    v___x_1515_ = v_reuseFailAlloc_1523_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1471_ == 0 {
                    lean_ctor_set(v___x_1470_, 0, v___x_1515_);
                    v___x_1517_ = v___x_1470_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1515_);
                    lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_mvarId_1468_);
                    v___x_1517_ = v_reuseFailAlloc_1522_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_1518_ = lean_st_ref_set(v_a_1400_, v___x_1517_);
                if v_isShared_1463_ == 0 {
                    lean_ctor_set(v___x_1462_, 0, v___x_1508_);
                    v___x_1520_ = v___x_1462_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1508_);
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
                    v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
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
    mut v_f_1553_: *mut LeanObject,
    mut v_a_1554_: *mut LeanObject,
    mut v_a_1555_: *mut LeanObject,
    mut v_a_1556_: *mut LeanObject,
    mut v_a_1557_: *mut LeanObject,
    mut v_a_1558_: *mut LeanObject,
    mut v_a_1559_: *mut LeanObject,
    mut v_a_1560_: *mut LeanObject,
    mut v_a_1561_: *mut LeanObject,
    mut v_a_1562_: *mut LeanObject,
    mut v_a_1563_: *mut LeanObject,
    mut v_a_1564_: *mut LeanObject,
    mut v_a_1565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1566_: *mut LeanObject = core::ptr::null_mut();
    v_res_1566_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(
        v_f_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_,
        v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_,
    );
    lean_dec(v_a_1564_);
    lean_dec_ref(v_a_1563_);
    lean_dec(v_a_1562_);
    lean_dec_ref(v_a_1561_);
    lean_dec(v_a_1560_);
    lean_dec_ref(v_a_1559_);
    lean_dec(v_a_1558_);
    lean_dec_ref(v_a_1557_);
    lean_dec(v_a_1556_);
    lean_dec(v_a_1555_);
    return v_res_1566_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(
    mut v_00_u03b2_1567_: *mut LeanObject,
    mut v_x_1568_: *mut LeanObject,
    mut v_x_1569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    v___x_1570_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___redArg(v_x_1568_, v_x_1569_);
    return v___x_1570_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1___boxed(
    mut v_00_u03b2_1571_: *mut LeanObject,
    mut v_x_1572_: *mut LeanObject,
    mut v_x_1573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1574_: *mut LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1(v_00_u03b2_1571_, v_x_1572_, v_x_1573_);
    lean_dec_ref(v_x_1573_);
    lean_dec_ref(v_x_1572_);
    return v_res_1574_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2(
    mut v_00_u03b2_1575_: *mut LeanObject,
    mut v_x_1576_: *mut LeanObject,
    mut v_x_1577_: *mut LeanObject,
    mut v_x_1578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    v___x_1579_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_x_1576_, v_x_1577_, v_x_1578_);
    return v___x_1579_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(
    mut v_00_u03b2_1580_: *mut LeanObject,
    mut v_x_1581_: *mut LeanObject,
    mut v_x_1582_: usize,
    mut v_x_1583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg(v_x_1581_, v_x_1582_, v_x_1583_);
    return v___x_1584_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___boxed(
    mut v_00_u03b2_1585_: *mut LeanObject,
    mut v_x_1586_: *mut LeanObject,
    mut v_x_1587_: *mut LeanObject,
    mut v_x_1588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_10143__boxed_1589_: usize = 0;
    let mut v_res_1590_: *mut LeanObject = core::ptr::null_mut();
    v_x_10143__boxed_1589_ = lean_unbox_usize(v_x_1587_);
    lean_dec(v_x_1587_);
    v_res_1590_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1(v_00_u03b2_1585_, v_x_1586_, v_x_10143__boxed_1589_, v_x_1588_);
    lean_dec_ref(v_x_1588_);
    lean_dec_ref(v_x_1586_);
    return v_res_1590_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(
    mut v_00_u03b2_1591_: *mut LeanObject,
    mut v_x_1592_: *mut LeanObject,
    mut v_x_1593_: usize,
    mut v_x_1594_: usize,
    mut v_x_1595_: *mut LeanObject,
    mut v_x_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___redArg(v_x_1592_, v_x_1593_, v_x_1594_, v_x_1595_, v_x_1596_);
    return v___x_1597_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3___boxed(
    mut v_00_u03b2_1598_: *mut LeanObject,
    mut v_x_1599_: *mut LeanObject,
    mut v_x_1600_: *mut LeanObject,
    mut v_x_1601_: *mut LeanObject,
    mut v_x_1602_: *mut LeanObject,
    mut v_x_1603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_10154__boxed_1604_: usize = 0;
    let mut v_x_10155__boxed_1605_: usize = 0;
    let mut v_res_1606_: *mut LeanObject = core::ptr::null_mut();
    v_x_10154__boxed_1604_ = lean_unbox_usize(v_x_1600_);
    lean_dec(v_x_1600_);
    v_x_10155__boxed_1605_ = lean_unbox_usize(v_x_1601_);
    lean_dec(v_x_1601_);
    v_res_1606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3(v_00_u03b2_1598_, v_x_1599_, v_x_10154__boxed_1604_, v_x_10155__boxed_1605_, v_x_1602_, v_x_1603_);
    return v_res_1606_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(
    mut v_00_u03b2_1607_: *mut LeanObject,
    mut v_keys_1608_: *mut LeanObject,
    mut v_vals_1609_: *mut LeanObject,
    mut v_heq_1610_: *mut LeanObject,
    mut v_i_1611_: *mut LeanObject,
    mut v_k_1612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    v___x_1613_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___redArg(v_keys_1608_, v_vals_1609_, v_i_1611_, v_k_1612_);
    return v___x_1613_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_1614_: *mut LeanObject,
    mut v_keys_1615_: *mut LeanObject,
    mut v_vals_1616_: *mut LeanObject,
    mut v_heq_1617_: *mut LeanObject,
    mut v_i_1618_: *mut LeanObject,
    mut v_k_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1620_: *mut LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1_spec__2(v_00_u03b2_1614_, v_keys_1615_, v_vals_1616_, v_heq_1617_, v_i_1618_, v_k_1619_);
    lean_dec_ref(v_k_1619_);
    lean_dec_ref(v_vals_1616_);
    lean_dec_ref(v_keys_1615_);
    return v_res_1620_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5(
    mut v_00_u03b2_1621_: *mut LeanObject,
    mut v_n_1622_: *mut LeanObject,
    mut v_k_1623_: *mut LeanObject,
    mut v_v_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5___redArg(v_n_1622_, v_k_1623_, v_v_1624_);
    return v___x_1625_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(
    mut v_00_u03b2_1626_: *mut LeanObject,
    mut v_depth_1627_: usize,
    mut v_keys_1628_: *mut LeanObject,
    mut v_vals_1629_: *mut LeanObject,
    mut v_heq_1630_: *mut LeanObject,
    mut v_i_1631_: *mut LeanObject,
    mut v_entries_1632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    v___x_1633_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___redArg(v_depth_1627_, v_keys_1628_, v_vals_1629_, v_i_1631_, v_entries_1632_);
    return v___x_1633_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6___boxed(
    mut v_00_u03b2_1634_: *mut LeanObject,
    mut v_depth_1635_: *mut LeanObject,
    mut v_keys_1636_: *mut LeanObject,
    mut v_vals_1637_: *mut LeanObject,
    mut v_heq_1638_: *mut LeanObject,
    mut v_i_1639_: *mut LeanObject,
    mut v_entries_1640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1641_: usize = 0;
    let mut v_res_1642_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1641_ = lean_unbox_usize(v_depth_1635_);
    lean_dec(v_depth_1635_);
    v_res_1642_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__6(v_00_u03b2_1634_, v_depth_boxed_1641_, v_keys_1636_, v_vals_1637_, v_heq_1638_, v_i_1639_, v_entries_1640_);
    lean_dec_ref(v_vals_1637_);
    lean_dec_ref(v_keys_1636_);
    return v_res_1642_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6(
    mut v_00_u03b2_1643_: *mut LeanObject,
    mut v_x_1644_: *mut LeanObject,
    mut v_x_1645_: *mut LeanObject,
    mut v_x_1646_: *mut LeanObject,
    mut v_x_1647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    v___x_1648_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2_spec__3_spec__5_spec__6___redArg(v_x_1644_, v_x_1645_, v_x_1646_, v_x_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(
    mut v_msgData_1649_: *mut LeanObject,
    mut v___y_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
    mut v___y_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    v___x_1655_ = lean_st_ref_get(v___y_1653_);
    v_env_1656_ = lean_ctor_get(v___x_1655_, 0);
    lean_inc_ref(v_env_1656_);
    lean_dec(v___x_1655_);
    v___x_1657_ = lean_st_ref_get(v___y_1651_);
    v_mctx_1658_ = lean_ctor_get(v___x_1657_, 0);
    lean_inc_ref(v_mctx_1658_);
    lean_dec(v___x_1657_);
    v_lctx_1659_ = lean_ctor_get(v___y_1650_, 2);
    v_options_1660_ = lean_ctor_get(v___y_1652_, 2);
    lean_inc_ref(v_options_1660_);
    lean_inc_ref(v_lctx_1659_);
    v___x_1661_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1661_, 0, v_env_1656_);
    lean_ctor_set(v___x_1661_, 1, v_mctx_1658_);
    lean_ctor_set(v___x_1661_, 2, v_lctx_1659_);
    lean_ctor_set(v___x_1661_, 3, v_options_1660_);
    v___x_1662_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1662_, 0, v___x_1661_);
    lean_ctor_set(v___x_1662_, 1, v_msgData_1649_);
    v___x_1663_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1663_, 0, v___x_1662_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0___boxed(
    mut v_msgData_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1670_: *mut LeanObject = core::ptr::null_mut();
    v_res_1670_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msgData_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
    lean_dec(v___y_1668_);
    lean_dec_ref(v___y_1667_);
    lean_dec(v___y_1666_);
    lean_dec_ref(v___y_1665_);
    return v_res_1670_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: f64 = 0.0;
    v___x_1671_ = lean_unsigned_to_nat(0);
    v___x_1672_ = lean_float_of_nat(v___x_1671_);
    return v___x_1672_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(
    mut v_cls_1676_: *mut LeanObject,
    mut v_msg_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1688_: u8 = 0;
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1701_: u8 = 0;
    let mut v_tid_1702_: u64 = 0;
    let mut v_traces_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: f64 = 0.0;
    let mut v___x_1709_: u8 = 0;
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_isSharedCheck_1728_: u8 = 0;
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1683_ = lean_ctor_get(v___y_1680_, 5);
                v___x_1684_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0_spec__0(v_msg_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
                v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
                v_isSharedCheck_1729_ = (!lean_is_exclusive(v___x_1684_)) as u8;
                if v_isSharedCheck_1729_ == 0 {
                    v___x_1687_ = v___x_1684_;
                    v_isShared_1688_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1685_);
                    lean_dec(v___x_1684_);
                    v___x_1687_ = lean_box(0);
                    v_isShared_1688_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1689_ = lean_st_ref_take(v___y_1681_);
                v_traceState_1690_ = lean_ctor_get(v___x_1689_, 4);
                v_env_1691_ = lean_ctor_get(v___x_1689_, 0);
                v_nextMacroScope_1692_ = lean_ctor_get(v___x_1689_, 1);
                v_ngen_1693_ = lean_ctor_get(v___x_1689_, 2);
                v_auxDeclNGen_1694_ = lean_ctor_get(v___x_1689_, 3);
                v_cache_1695_ = lean_ctor_get(v___x_1689_, 5);
                v_messages_1696_ = lean_ctor_get(v___x_1689_, 6);
                v_infoState_1697_ = lean_ctor_get(v___x_1689_, 7);
                v_snapshotTasks_1698_ = lean_ctor_get(v___x_1689_, 8);
                v_isSharedCheck_1728_ = (!lean_is_exclusive(v___x_1689_)) as u8;
                if v_isSharedCheck_1728_ == 0 {
                    v___x_1700_ = v___x_1689_;
                    v_isShared_1701_ = v_isSharedCheck_1728_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1698_);
                    lean_inc(v_infoState_1697_);
                    lean_inc(v_messages_1696_);
                    lean_inc(v_cache_1695_);
                    lean_inc(v_traceState_1690_);
                    lean_inc(v_auxDeclNGen_1694_);
                    lean_inc(v_ngen_1693_);
                    lean_inc(v_nextMacroScope_1692_);
                    lean_inc(v_env_1691_);
                    lean_dec(v___x_1689_);
                    v___x_1700_ = lean_box(0);
                    v_isShared_1701_ = v_isSharedCheck_1728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1702_ = lean_ctor_get_uint64(
                    v_traceState_1690_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_1703_ = lean_ctor_get(v_traceState_1690_, 0);
                v_isSharedCheck_1727_ = (!lean_is_exclusive(v_traceState_1690_)) as u8;
                if v_isSharedCheck_1727_ == 0 {
                    v___x_1705_ = v_traceState_1690_;
                    v_isShared_1706_ = v_isSharedCheck_1727_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_1703_);
                    lean_dec(v_traceState_1690_);
                    v___x_1705_ = lean_box(0);
                    v_isShared_1706_ = v_isSharedCheck_1727_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1707_ = lean_box(0);
                v___x_1708_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__0);
                v___x_1709_ = 0;
                v___x_1710_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__1;
                v___x_1711_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_1711_, 0, v_cls_1676_);
                lean_ctor_set(v___x_1711_, 1, v___x_1707_);
                lean_ctor_set(v___x_1711_, 2, v___x_1710_);
                lean_ctor_set_float(
                    v___x_1711_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1708_,
                );
                lean_ctor_set_float(
                    v___x_1711_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_1708_,
                );
                lean_ctor_set_uint8(
                    v___x_1711_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_1709_,
                );
                v___x_1712_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg___closed__2;
                v___x_1713_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_1713_, 0, v___x_1711_);
                lean_ctor_set(v___x_1713_, 1, v_a_1685_);
                lean_ctor_set(v___x_1713_, 2, v___x_1712_);
                lean_inc(v_ref_1683_);
                v___x_1714_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1714_, 0, v_ref_1683_);
                lean_ctor_set(v___x_1714_, 1, v___x_1713_);
                v___x_1715_ = l_Lean_PersistentArray_push___redArg(v_traces_1703_, v___x_1714_);
                if v_isShared_1706_ == 0 {
                    lean_ctor_set(v___x_1705_, 0, v___x_1715_);
                    v___x_1717_ = v___x_1705_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1715_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_1726_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_1702_,
                    );
                    v___x_1717_ = v_reuseFailAlloc_1726_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1701_ == 0 {
                    lean_ctor_set(v___x_1700_, 4, v___x_1717_);
                    v___x_1719_ = v___x_1700_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_env_1691_);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_nextMacroScope_1692_);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_ngen_1693_);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_auxDeclNGen_1694_);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 4, v___x_1717_);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 5, v_cache_1695_);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 6, v_messages_1696_);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 7, v_infoState_1697_);
                    lean_ctor_set(v_reuseFailAlloc_1725_, 8, v_snapshotTasks_1698_);
                    v___x_1719_ = v_reuseFailAlloc_1725_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1720_ = lean_st_ref_set(v___y_1681_, v___x_1719_);
                v___x_1721_ = lean_box(0);
                if v_isShared_1688_ == 0 {
                    lean_ctor_set(v___x_1687_, 0, v___x_1721_);
                    v___x_1723_ = v___x_1687_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
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
    mut v_cls_1730_: *mut LeanObject,
    mut v_msg_1731_: *mut LeanObject,
    mut v___y_1732_: *mut LeanObject,
    mut v___y_1733_: *mut LeanObject,
    mut v___y_1734_: *mut LeanObject,
    mut v___y_1735_: *mut LeanObject,
    mut v___y_1736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1737_: *mut LeanObject = core::ptr::null_mut();
    v_res_1737_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(
        v_cls_1730_,
        v_msg_1731_,
        v___y_1732_,
        v___y_1733_,
        v___y_1734_,
        v___y_1735_,
    );
    lean_dec(v___y_1735_);
    lean_dec_ref(v___y_1734_);
    lean_dec(v___y_1733_);
    lean_dec_ref(v___y_1732_);
    return v_res_1737_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkInjEq___closed__6() -> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ = l_Lean_Meta_Grind_mkInjEq___closed__3;
    v___x_1749_ = l_Lean_Meta_Grind_mkInjEq___closed__5;
    v___x_1750_ = l_Lean_Name_append(v___x_1749_, v___x_1748_);
    return v___x_1750_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkInjEq___closed__8() -> *mut LeanObject {
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    v___x_1752_ = l_Lean_Meta_Grind_mkInjEq___closed__7;
    v___x_1753_ = l_Lean_stringToMessageData(v___x_1752_);
    return v___x_1753_;
}
pub unsafe fn l_Lean_Meta_Grind_mkInjEq(
    mut v_e_1754_: *mut LeanObject,
    mut v_a_1755_: *mut LeanObject,
    mut v_a_1756_: *mut LeanObject,
    mut v_a_1757_: *mut LeanObject,
    mut v_a_1758_: *mut LeanObject,
    mut v_a_1759_: *mut LeanObject,
    mut v_a_1760_: *mut LeanObject,
    mut v_a_1761_: *mut LeanObject,
    mut v_a_1762_: *mut LeanObject,
    mut v_a_1763_: *mut LeanObject,
    mut v_a_1764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1772_: u8 = 0;
    let mut v_val_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: u8 = 0;
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1795_: u8 = 0;
    let mut v_inheritedTraceOptions_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_isSharedCheck_1816_: u8 = 0;
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut v_a_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1825_: u8 = 0;
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1829_: u8 = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_1754_) == 5 {
                    v_fn_1766_ = lean_ctor_get(v_e_1754_, 0);
                    v_arg_1767_ = lean_ctor_get(v_e_1754_, 1);
                    lean_inc_ref_n(v_arg_1767_, 2);
                    lean_inc_ref(v_fn_1766_);
                    v___x_1768_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f(v_fn_1766_, v_arg_1767_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
                    if lean_obj_tag(v___x_1768_) == 0 {
                        v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
                        v_isSharedCheck_1821_ = (!lean_is_exclusive(v___x_1768_)) as u8;
                        if v_isSharedCheck_1821_ == 0 {
                            v___x_1771_ = v___x_1768_;
                            v_isShared_1772_ = v_isSharedCheck_1821_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1769_);
                            lean_dec(v___x_1768_);
                            v___x_1771_ = lean_box(0);
                            v_isShared_1772_ = v_isSharedCheck_1821_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_arg_1767_);
                        lean_dec_ref_known(v_e_1754_, 2);
                        v_a_1822_ = lean_ctor_get(v___x_1768_, 0);
                        v_isSharedCheck_1829_ = (!lean_is_exclusive(v___x_1768_)) as u8;
                        if v_isSharedCheck_1829_ == 0 {
                            v___x_1824_ = v___x_1768_;
                            v_isShared_1825_ = v_isSharedCheck_1829_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1822_);
                            lean_dec(v___x_1768_);
                            v___x_1824_ = lean_box(0);
                            v_isShared_1825_ = v_isSharedCheck_1829_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_1754_);
                    v___x_1830_ = lean_box(0);
                    v___x_1831_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1831_, 0, v___x_1830_);
                    return v___x_1831_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1769_) == 1 {
                    lean_del_object(v___x_1771_);
                    v_val_1773_ = lean_ctor_get(v_a_1769_, 0);
                    lean_inc(v_val_1773_);
                    lean_dec_ref_known(v_a_1769_, 1);
                    v_fst_1774_ = lean_ctor_get(v_val_1773_, 0);
                    v_snd_1775_ = lean_ctor_get(v_val_1773_, 1);
                    v_isSharedCheck_1816_ = (!lean_is_exclusive(v_val_1773_)) as u8;
                    if v_isSharedCheck_1816_ == 0 {
                        v___x_1777_ = v_val_1773_;
                        v_isShared_1778_ = v_isSharedCheck_1816_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_1775_);
                        lean_inc(v_fst_1774_);
                        lean_dec(v_val_1773_);
                        v___x_1777_ = lean_box(0);
                        v_isShared_1778_ = v_isSharedCheck_1816_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1769_);
                    lean_dec_ref(v_arg_1767_);
                    lean_dec_ref_known(v_e_1754_, 2);
                    v___x_1817_ = lean_box(0);
                    if v_isShared_1772_ == 0 {
                        lean_ctor_set(v___x_1771_, 0, v___x_1817_);
                        v___x_1819_ = v___x_1771_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                        v___x_1819_ = v_reuseFailAlloc_1820_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1779_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1754_, v_a_1755_);
                if lean_obj_tag(v___x_1779_) == 0 {
                    v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
                    lean_inc(v_a_1780_);
                    lean_dec_ref_known(v___x_1779_, 1);
                    v___x_1781_ = l_Lean_Expr_app___override(v_fst_1774_, v_e_1754_);
                    v___x_1792_ = lean_box(0);
                    lean_inc(v_a_1764_);
                    lean_inc_ref(v_a_1763_);
                    lean_inc(v_a_1762_);
                    lean_inc_ref(v_a_1761_);
                    lean_inc(v_a_1760_);
                    lean_inc_ref(v_a_1759_);
                    lean_inc(v_a_1758_);
                    lean_inc_ref(v_a_1757_);
                    lean_inc(v_a_1756_);
                    lean_inc(v_a_1755_);
                    lean_inc_ref(v___x_1781_);
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
                    if lean_obj_tag(v___x_1793_) == 0 {
                        lean_dec_ref_known(v___x_1793_, 1);
                        v_options_1794_ = lean_ctor_get(v_a_1763_, 2);
                        v_hasTrace_1795_ = lean_ctor_get_uint8(
                            v_options_1794_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_hasTrace_1795_ == 0 {
                            lean_del_object(v___x_1777_);
                            v___y_1783_ = v_a_1755_;
                            v___y_1784_ = v_a_1757_;
                            v___y_1785_ = v_a_1761_;
                            v___y_1786_ = v_a_1762_;
                            v___y_1787_ = v_a_1763_;
                            v___y_1788_ = v_a_1764_;
                            state = 3;
                            continue;
                        } else {
                            v_inheritedTraceOptions_1796_ = lean_ctor_get(v_a_1763_, 13);
                            v___x_1797_ = l_Lean_Meta_Grind_mkInjEq___closed__3;
                            v___x_1798_ = lean_obj_once(
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
                                lean_del_object(v___x_1777_);
                                v___y_1783_ = v_a_1755_;
                                v___y_1784_ = v_a_1757_;
                                v___y_1785_ = v_a_1761_;
                                v___y_1786_ = v_a_1762_;
                                v___y_1787_ = v_a_1763_;
                                v___y_1788_ = v_a_1764_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc_ref(v___x_1781_);
                                v___x_1800_ = l_Lean_MessageData_ofExpr(v___x_1781_);
                                v___x_1801_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkInjEq___closed__8),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_mkInjEq___closed__8_once
                                    ),
                                    _init_l_Lean_Meta_Grind_mkInjEq___closed__8,
                                );
                                if v_isShared_1778_ == 0 {
                                    lean_ctor_set_tag(v___x_1777_, 7);
                                    lean_ctor_set(v___x_1777_, 1, v___x_1801_);
                                    lean_ctor_set(v___x_1777_, 0, v___x_1800_);
                                    v___x_1803_ = v___x_1777_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1807_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1800_);
                                    lean_ctor_set(v_reuseFailAlloc_1807_, 1, v___x_1801_);
                                    v___x_1803_ = v_reuseFailAlloc_1807_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_1781_);
                        lean_del_object(v___x_1777_);
                        lean_dec(v_snd_1775_);
                        lean_dec_ref(v_arg_1767_);
                        return v___x_1793_;
                    }
                } else {
                    lean_del_object(v___x_1777_);
                    lean_dec(v_snd_1775_);
                    lean_dec(v_fst_1774_);
                    lean_dec_ref(v_arg_1767_);
                    lean_dec_ref_known(v_e_1754_, 2);
                    v_a_1808_ = lean_ctor_get(v___x_1779_, 0);
                    v_isSharedCheck_1815_ = (!lean_is_exclusive(v___x_1779_)) as u8;
                    if v_isSharedCheck_1815_ == 0 {
                        v___x_1810_ = v___x_1779_;
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1808_);
                        lean_dec(v___x_1779_);
                        v___x_1810_ = lean_box(0);
                        v_isShared_1811_ = v_isSharedCheck_1815_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc_ref(v_arg_1767_);
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
                lean_inc_ref(v_arg_1767_);
                v___x_1804_ = l_Lean_MessageData_ofExpr(v_arg_1767_);
                v___x_1805_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1805_, 0, v___x_1803_);
                lean_ctor_set(v___x_1805_, 1, v___x_1804_);
                v___x_1806_ = l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0___redArg(
                    v___x_1797_,
                    v___x_1805_,
                    v_a_1761_,
                    v_a_1762_,
                    v_a_1763_,
                    v_a_1764_,
                );
                if lean_obj_tag(v___x_1806_) == 0 {
                    lean_dec_ref_known(v___x_1806_, 1);
                    v___y_1783_ = v_a_1755_;
                    v___y_1784_ = v_a_1757_;
                    v___y_1785_ = v_a_1761_;
                    v___y_1786_ = v_a_1762_;
                    v___y_1787_ = v_a_1763_;
                    v___y_1788_ = v_a_1764_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref(v___x_1781_);
                    lean_dec(v_snd_1775_);
                    lean_dec_ref(v_arg_1767_);
                    return v___x_1806_;
                }
            }
            5 => {
                if v_isShared_1811_ == 0 {
                    v___x_1813_ = v___x_1810_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
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
                    v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
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
    mut v_e_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
    mut v_a_1839_: *mut LeanObject,
    mut v_a_1840_: *mut LeanObject,
    mut v_a_1841_: *mut LeanObject,
    mut v_a_1842_: *mut LeanObject,
    mut v_a_1843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1844_: *mut LeanObject = core::ptr::null_mut();
    v_res_1844_ = l_Lean_Meta_Grind_mkInjEq(
        v_e_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_,
        v_a_1840_, v_a_1841_, v_a_1842_,
    );
    lean_dec(v_a_1842_);
    lean_dec_ref(v_a_1841_);
    lean_dec(v_a_1840_);
    lean_dec_ref(v_a_1839_);
    lean_dec(v_a_1838_);
    lean_dec_ref(v_a_1837_);
    lean_dec(v_a_1836_);
    lean_dec_ref(v_a_1835_);
    lean_dec(v_a_1834_);
    lean_dec(v_a_1833_);
    return v_res_1844_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_mkInjEq_spec__0(
    mut v_cls_1845_: *mut LeanObject,
    mut v_msg_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_cls_1859_: *mut LeanObject,
    mut v_msg_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1872_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1870_);
    lean_dec_ref(v___y_1869_);
    lean_dec(v___y_1868_);
    lean_dec_ref(v___y_1867_);
    lean_dec(v___y_1866_);
    lean_dec_ref(v___y_1865_);
    lean_dec(v___y_1864_);
    lean_dec_ref(v___y_1863_);
    lean_dec(v___y_1862_);
    lean_dec(v___y_1861_);
    return v_res_1872_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(
    mut v_keys_1873_: *mut LeanObject,
    mut v_vals_1874_: *mut LeanObject,
    mut v_i_1875_: *mut LeanObject,
    mut v_k_1876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: u8 = 0;
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1877_ = lean_array_get_size(v_keys_1873_);
                v___x_1878_ = lean_nat_dec_lt(v_i_1875_, v___x_1877_);
                if v___x_1878_ == 0 {
                    lean_dec(v_i_1875_);
                    v___x_1879_ = lean_box(0);
                    return v___x_1879_;
                } else {
                    v_k_x27_1880_ = lean_array_fget_borrowed(v_keys_1873_, v_i_1875_);
                    v___x_1881_ = l_Lean_instBEqHeadIndex_beq(v_k_1876_, v_k_x27_1880_);
                    if v___x_1881_ == 0 {
                        v___x_1882_ = lean_unsigned_to_nat(1);
                        v___x_1883_ = lean_nat_add(v_i_1875_, v___x_1882_);
                        lean_dec(v_i_1875_);
                        v_i_1875_ = v___x_1883_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1885_ = lean_array_fget_borrowed(v_vals_1874_, v_i_1875_);
                        lean_dec(v_i_1875_);
                        lean_inc(v___x_1885_);
                        v___x_1886_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1886_, 0, v___x_1885_);
                        return v___x_1886_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_keys_1887_: *mut LeanObject,
    mut v_vals_1888_: *mut LeanObject,
    mut v_i_1889_: *mut LeanObject,
    mut v_k_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1891_: *mut LeanObject = core::ptr::null_mut();
    v_res_1891_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_1887_, v_vals_1888_, v_i_1889_, v_k_1890_);
    lean_dec(v_k_1890_);
    lean_dec_ref(v_vals_1888_);
    lean_dec_ref(v_keys_1887_);
    return v_res_1891_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(
    mut v_x_1892_: *mut LeanObject,
    mut v_x_1893_: usize,
    mut v_x_1894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: usize = 0;
    let mut v___x_1898_: usize = 0;
    let mut v___x_1899_: usize = 0;
    let mut v_j_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: usize = 0;
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1892_) == 0 {
                    v_es_1895_ = lean_ctor_get(v_x_1892_, 0);
                    v___x_1896_ = lean_box(2);
                    v___x_1897_ = 5usize;
                    v___x_1898_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__1_spec__1___redArg___closed__1);
                    v___x_1899_ = lean_usize_land(v_x_1893_, v___x_1898_);
                    v_j_1900_ = lean_usize_to_nat(v___x_1899_);
                    v___x_1901_ = lean_array_get_borrowed(v___x_1896_, v_es_1895_, v_j_1900_);
                    lean_dec(v_j_1900_);
                    match lean_obj_tag(v___x_1901_) {
                        0 => {
                            v_key_1902_ = lean_ctor_get(v___x_1901_, 0);
                            v_val_1903_ = lean_ctor_get(v___x_1901_, 1);
                            v___x_1904_ = l_Lean_instBEqHeadIndex_beq(v_x_1894_, v_key_1902_);
                            if v___x_1904_ == 0 {
                                v___x_1905_ = lean_box(0);
                                return v___x_1905_;
                            } else {
                                lean_inc(v_val_1903_);
                                v___x_1906_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1906_, 0, v_val_1903_);
                                return v___x_1906_;
                            }
                        }
                        1 => {
                            v_node_1907_ = lean_ctor_get(v___x_1901_, 0);
                            v___x_1908_ = lean_usize_shift_right(v_x_1893_, v___x_1897_);
                            v_x_1892_ = v_node_1907_;
                            v_x_1893_ = v___x_1908_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1910_ = lean_box(0);
                            return v___x_1910_;
                        }
                    }
                } else {
                    v_ks_1911_ = lean_ctor_get(v_x_1892_, 0);
                    v_vs_1912_ = lean_ctor_get(v_x_1892_, 1);
                    v___x_1913_ = lean_unsigned_to_nat(0);
                    v___x_1914_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_ks_1911_, v_vs_1912_, v___x_1913_, v_x_1894_);
                    return v___x_1914_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg___boxed(
    mut v_x_1915_: *mut LeanObject,
    mut v_x_1916_: *mut LeanObject,
    mut v_x_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9714__boxed_1918_: usize = 0;
    let mut v_res_1919_: *mut LeanObject = core::ptr::null_mut();
    v_x_9714__boxed_1918_ = lean_unbox_usize(v_x_1916_);
    lean_dec(v_x_1916_);
    v_res_1919_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_1915_, v_x_9714__boxed_1918_, v_x_1917_);
    lean_dec(v_x_1917_);
    lean_dec_ref(v_x_1915_);
    return v_res_1919_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(
    mut v_x_1920_: *mut LeanObject,
    mut v_x_1921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1922_: u64 = 0;
    let mut v___x_1923_: usize = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    v___x_1922_ = l_Lean_HeadIndex_hash(v_x_1921_);
    v___x_1923_ = lean_uint64_to_usize(v___x_1922_);
    v___x_1924_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_1920_, v___x_1923_, v_x_1921_);
    return v___x_1924_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg___boxed(
    mut v_x_1925_: *mut LeanObject,
    mut v_x_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1927_: *mut LeanObject = core::ptr::null_mut();
    v_res_1927_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_1925_, v_x_1926_);
    lean_dec(v_x_1926_);
    lean_dec_ref(v_x_1925_);
    return v_res_1927_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(
    mut v_f_1928_: *mut LeanObject,
    mut v_as_x27_1929_: *mut LeanObject,
    mut v_b_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
    mut v___y_1933_: *mut LeanObject,
    mut v___y_1934_: *mut LeanObject,
    mut v___y_1935_: *mut LeanObject,
    mut v___y_1936_: *mut LeanObject,
    mut v___y_1937_: *mut LeanObject,
    mut v___y_1938_: *mut LeanObject,
    mut v___y_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1947_: u8 = 0;
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_1929_) == 0 {
                    v___x_1942_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1942_, 0, v_b_1930_);
                    return v___x_1942_;
                } else {
                    v_head_1943_ = lean_ctor_get(v_as_x27_1929_, 0);
                    v_tail_1944_ = lean_ctor_get(v_as_x27_1929_, 1);
                    v___x_1945_ = lean_box(0);
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
                        lean_dec_ref(v___x_1952_);
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
                    lean_inc(v_head_1943_);
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
                    if lean_obj_tag(v___x_1949_) == 0 {
                        lean_dec_ref_known(v___x_1949_, 1);
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
    mut v_f_1954_: *mut LeanObject,
    mut v_as_x27_1955_: *mut LeanObject,
    mut v_b_1956_: *mut LeanObject,
    mut v___y_1957_: *mut LeanObject,
    mut v___y_1958_: *mut LeanObject,
    mut v___y_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
    mut v___y_1963_: *mut LeanObject,
    mut v___y_1964_: *mut LeanObject,
    mut v___y_1965_: *mut LeanObject,
    mut v___y_1966_: *mut LeanObject,
    mut v___y_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1968_: *mut LeanObject = core::ptr::null_mut();
    v_res_1968_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_1954_, v_as_x27_1955_, v_b_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_);
    lean_dec(v___y_1966_);
    lean_dec_ref(v___y_1965_);
    lean_dec(v___y_1964_);
    lean_dec_ref(v___y_1963_);
    lean_dec(v___y_1962_);
    lean_dec_ref(v___y_1961_);
    lean_dec(v___y_1960_);
    lean_dec_ref(v___y_1959_);
    lean_dec(v___y_1958_);
    lean_dec(v___y_1957_);
    lean_dec(v_as_x27_1955_);
    lean_dec_ref(v_f_1954_);
    return v_res_1968_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(
    mut v_us_1969_: *mut LeanObject,
    mut v_00_u03b1_1970_: *mut LeanObject,
    mut v_00_u03b2_1971_: *mut LeanObject,
    mut v_f_1972_: *mut LeanObject,
    mut v_h_1973_: *mut LeanObject,
    mut v_a_1974_: *mut LeanObject,
    mut v_a_1975_: *mut LeanObject,
    mut v_a_1976_: *mut LeanObject,
    mut v_a_1977_: *mut LeanObject,
    mut v_a_1978_: *mut LeanObject,
    mut v_a_1979_: *mut LeanObject,
    mut v_a_1980_: *mut LeanObject,
    mut v_a_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
    mut v_a_1983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inj_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1991_: u8 = 0;
    let mut v_nextDeclIdx_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprs_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_parents_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrTable_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_appMap_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newFacts_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_2000_: u8 = 0;
    let mut v_nextIdx_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facts_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extThms_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematch_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_split_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_clean_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sstates_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v_thms_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fns_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_unused_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_appMap_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2049_: u8 = 0;
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_unused_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v_unused_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1985_ = lean_st_ref_take(v_a_1974_);
                v_toGoalState_1986_ = lean_ctor_get(v___x_1985_, 0);
                lean_inc_ref(v_toGoalState_1986_);
                v_inj_1987_ = lean_ctor_get(v_toGoalState_1986_, 13);
                lean_inc_ref(v_inj_1987_);
                v_mvarId_1988_ = lean_ctor_get(v___x_1985_, 1);
                v_isSharedCheck_2052_ = (!lean_is_exclusive(v___x_1985_)) as u8;
                if v_isSharedCheck_2052_ == 0 {
                    v_unused_2053_ = lean_ctor_get(v___x_1985_, 0);
                    lean_dec(v_unused_2053_);
                    v___x_1990_ = v___x_1985_;
                    v_isShared_1991_ = v_isSharedCheck_2052_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_mvarId_1988_);
                    lean_dec(v___x_1985_);
                    v___x_1990_ = lean_box(0);
                    v_isShared_1991_ = v_isSharedCheck_2052_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_nextDeclIdx_1992_ = lean_ctor_get(v_toGoalState_1986_, 0);
                v_enodeMap_1993_ = lean_ctor_get(v_toGoalState_1986_, 1);
                v_exprs_1994_ = lean_ctor_get(v_toGoalState_1986_, 2);
                v_parents_1995_ = lean_ctor_get(v_toGoalState_1986_, 3);
                v_congrTable_1996_ = lean_ctor_get(v_toGoalState_1986_, 4);
                v_appMap_1997_ = lean_ctor_get(v_toGoalState_1986_, 5);
                v_indicesFound_1998_ = lean_ctor_get(v_toGoalState_1986_, 6);
                v_newFacts_1999_ = lean_ctor_get(v_toGoalState_1986_, 7);
                v_inconsistent_2000_ = lean_ctor_get_uint8(
                    v_toGoalState_1986_,
                    (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                );
                v_nextIdx_2001_ = lean_ctor_get(v_toGoalState_1986_, 8);
                v_newRawFacts_2002_ = lean_ctor_get(v_toGoalState_1986_, 9);
                v_facts_2003_ = lean_ctor_get(v_toGoalState_1986_, 10);
                v_extThms_2004_ = lean_ctor_get(v_toGoalState_1986_, 11);
                v_ematch_2005_ = lean_ctor_get(v_toGoalState_1986_, 12);
                v_split_2006_ = lean_ctor_get(v_toGoalState_1986_, 14);
                v_clean_2007_ = lean_ctor_get(v_toGoalState_1986_, 15);
                v_sstates_2008_ = lean_ctor_get(v_toGoalState_1986_, 16);
                v_isSharedCheck_2050_ = (!lean_is_exclusive(v_toGoalState_1986_)) as u8;
                if v_isSharedCheck_2050_ == 0 {
                    v_unused_2051_ = lean_ctor_get(v_toGoalState_1986_, 13);
                    lean_dec(v_unused_2051_);
                    v___x_2010_ = v_toGoalState_1986_;
                    v_isShared_2011_ = v_isSharedCheck_2050_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_sstates_2008_);
                    lean_inc(v_clean_2007_);
                    lean_inc(v_split_2006_);
                    lean_inc(v_ematch_2005_);
                    lean_inc(v_extThms_2004_);
                    lean_inc(v_facts_2003_);
                    lean_inc(v_newRawFacts_2002_);
                    lean_inc(v_nextIdx_2001_);
                    lean_inc(v_newFacts_1999_);
                    lean_inc(v_indicesFound_1998_);
                    lean_inc(v_appMap_1997_);
                    lean_inc(v_congrTable_1996_);
                    lean_inc(v_parents_1995_);
                    lean_inc(v_exprs_1994_);
                    lean_inc(v_enodeMap_1993_);
                    lean_inc(v_nextDeclIdx_1992_);
                    lean_dec(v_toGoalState_1986_);
                    v___x_2010_ = lean_box(0);
                    v_isShared_2011_ = v_isSharedCheck_2050_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_thms_2012_ = lean_ctor_get(v_inj_1987_, 0);
                v_fns_2013_ = lean_ctor_get(v_inj_1987_, 1);
                v_isSharedCheck_2049_ = (!lean_is_exclusive(v_inj_1987_)) as u8;
                if v_isSharedCheck_2049_ == 0 {
                    v___x_2015_ = v_inj_1987_;
                    v_isShared_2016_ = v_isSharedCheck_2049_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fns_2013_);
                    lean_inc(v_thms_2012_);
                    lean_dec(v_inj_1987_);
                    v___x_2015_ = lean_box(0);
                    v_isShared_2016_ = v_isSharedCheck_2049_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2017_ = lean_box(0);
                v___x_2018_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2018_, 0, v_us_1969_);
                lean_ctor_set(v___x_2018_, 1, v_00_u03b1_1970_);
                lean_ctor_set(v___x_2018_, 2, v_00_u03b2_1971_);
                lean_ctor_set(v___x_2018_, 3, v_h_1973_);
                lean_ctor_set(v___x_2018_, 4, v___x_2017_);
                lean_inc_ref(v_f_1972_);
                v___x_2019_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_getInvFor_x3f_spec__2___redArg(v_fns_2013_, v_f_1972_, v___x_2018_);
                if v_isShared_2016_ == 0 {
                    lean_ctor_set(v___x_2015_, 1, v___x_2019_);
                    v___x_2021_ = v___x_2015_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_thms_2012_);
                    lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2019_);
                    v___x_2021_ = v_reuseFailAlloc_2048_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2011_ == 0 {
                    lean_ctor_set(v___x_2010_, 13, v___x_2021_);
                    v___x_2023_ = v___x_2010_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 17, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_nextDeclIdx_1992_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_enodeMap_1993_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_exprs_1994_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_parents_1995_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 4, v_congrTable_1996_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 5, v_appMap_1997_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 6, v_indicesFound_1998_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 7, v_newFacts_1999_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 8, v_nextIdx_2001_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 9, v_newRawFacts_2002_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 10, v_facts_2003_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 11, v_extThms_2004_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 12, v_ematch_2005_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 13, v___x_2021_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 14, v_split_2006_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 15, v_clean_2007_);
                    lean_ctor_set(v_reuseFailAlloc_2047_, 16, v_sstates_2008_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2047_,
                        (core::mem::size_of::<*mut LeanObject>() * 17) as u32,
                        v_inconsistent_2000_,
                    );
                    v___x_2023_ = v_reuseFailAlloc_2047_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1991_ == 0 {
                    lean_ctor_set(v___x_1990_, 0, v___x_2023_);
                    v___x_2025_ = v___x_1990_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2023_);
                    lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_mvarId_1988_);
                    v___x_2025_ = v_reuseFailAlloc_2046_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2026_ = lean_st_ref_set(v_a_1974_, v___x_2025_);
                v___x_2027_ = lean_st_ref_get(v_a_1974_);
                v_toGoalState_2040_ = lean_ctor_get(v___x_2027_, 0);
                lean_inc_ref(v_toGoalState_2040_);
                lean_dec(v___x_2027_);
                v_appMap_2041_ = lean_ctor_get(v_toGoalState_2040_, 5);
                lean_inc_ref(v_appMap_2041_);
                lean_dec_ref(v_toGoalState_2040_);
                lean_inc_ref(v_f_1972_);
                v___x_2042_ = l_Lean_Expr_toHeadIndex(v_f_1972_);
                v___x_2043_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_appMap_2041_, v___x_2042_);
                lean_dec(v___x_2042_);
                lean_dec_ref(v_appMap_2041_);
                if lean_obj_tag(v___x_2043_) == 0 {
                    v___x_2044_ = lean_box(0);
                    v___y_2029_ = v___x_2044_;
                    state = 7;
                    continue;
                } else {
                    v_val_2045_ = lean_ctor_get(v___x_2043_, 0);
                    lean_inc(v_val_2045_);
                    lean_dec_ref_known(v___x_2043_, 1);
                    v___y_2029_ = v_val_2045_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2030_ = lean_box(0);
                v___x_2031_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_1972_, v___y_2029_, v___x_2030_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
                lean_dec(v___y_2029_);
                lean_dec_ref(v_f_1972_);
                if lean_obj_tag(v___x_2031_) == 0 {
                    v_isSharedCheck_2038_ = (!lean_is_exclusive(v___x_2031_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v_unused_2039_ = lean_ctor_get(v___x_2031_, 0);
                        lean_dec(v_unused_2039_);
                        v___x_2033_ = v___x_2031_;
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v___x_2031_);
                        v___x_2033_ = lean_box(0);
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
                    lean_ctor_set(v___x_2033_, 0, v___x_2030_);
                    v___x_2036_ = v___x_2033_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2030_);
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
    mut v_us_2054_: *mut LeanObject,
    mut v_00_u03b1_2055_: *mut LeanObject,
    mut v_00_u03b2_2056_: *mut LeanObject,
    mut v_f_2057_: *mut LeanObject,
    mut v_h_2058_: *mut LeanObject,
    mut v_a_2059_: *mut LeanObject,
    mut v_a_2060_: *mut LeanObject,
    mut v_a_2061_: *mut LeanObject,
    mut v_a_2062_: *mut LeanObject,
    mut v_a_2063_: *mut LeanObject,
    mut v_a_2064_: *mut LeanObject,
    mut v_a_2065_: *mut LeanObject,
    mut v_a_2066_: *mut LeanObject,
    mut v_a_2067_: *mut LeanObject,
    mut v_a_2068_: *mut LeanObject,
    mut v_a_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2070_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2068_);
    lean_dec_ref(v_a_2067_);
    lean_dec(v_a_2066_);
    lean_dec_ref(v_a_2065_);
    lean_dec(v_a_2064_);
    lean_dec_ref(v_a_2063_);
    lean_dec(v_a_2062_);
    lean_dec_ref(v_a_2061_);
    lean_dec(v_a_2060_);
    lean_dec(v_a_2059_);
    return v_res_2070_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(
    mut v_f_2071_: *mut LeanObject,
    mut v_as_2072_: *mut LeanObject,
    mut v_as_x27_2073_: *mut LeanObject,
    mut v_b_2074_: *mut LeanObject,
    mut v_a_2075_: *mut LeanObject,
    mut v___y_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
    mut v___y_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
    mut v___y_2082_: *mut LeanObject,
    mut v___y_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    v___x_2087_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___redArg(v_f_2071_, v_as_x27_2073_, v_b_2074_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
    return v___x_2087_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0___boxed(
    mut v_f_2088_: *mut LeanObject,
    mut v_as_2089_: *mut LeanObject,
    mut v_as_x27_2090_: *mut LeanObject,
    mut v_b_2091_: *mut LeanObject,
    mut v_a_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
    mut v___y_2097_: *mut LeanObject,
    mut v___y_2098_: *mut LeanObject,
    mut v___y_2099_: *mut LeanObject,
    mut v___y_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2104_: *mut LeanObject = core::ptr::null_mut();
    v_res_2104_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__0(v_f_2088_, v_as_2089_, v_as_x27_2090_, v_b_2091_, v_a_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
    lean_dec(v___y_2102_);
    lean_dec_ref(v___y_2101_);
    lean_dec(v___y_2100_);
    lean_dec_ref(v___y_2099_);
    lean_dec(v___y_2098_);
    lean_dec_ref(v___y_2097_);
    lean_dec(v___y_2096_);
    lean_dec_ref(v___y_2095_);
    lean_dec(v___y_2094_);
    lean_dec(v___y_2093_);
    lean_dec(v_as_x27_2090_);
    lean_dec(v_as_2089_);
    lean_dec_ref(v_f_2088_);
    return v_res_2104_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(
    mut v_00_u03b2_2105_: *mut LeanObject,
    mut v_x_2106_: *mut LeanObject,
    mut v_x_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    v___x_2108_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___redArg(v_x_2106_, v_x_2107_);
    return v___x_2108_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1___boxed(
    mut v_00_u03b2_2109_: *mut LeanObject,
    mut v_x_2110_: *mut LeanObject,
    mut v_x_2111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2112_: *mut LeanObject = core::ptr::null_mut();
    v_res_2112_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1(v_00_u03b2_2109_, v_x_2110_, v_x_2111_);
    lean_dec(v_x_2111_);
    lean_dec_ref(v_x_2110_);
    return v_res_2112_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(
    mut v_00_u03b2_2113_: *mut LeanObject,
    mut v_x_2114_: *mut LeanObject,
    mut v_x_2115_: usize,
    mut v_x_2116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    v___x_2117_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___redArg(v_x_2114_, v_x_2115_, v_x_2116_);
    return v___x_2117_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1___boxed(
    mut v_00_u03b2_2118_: *mut LeanObject,
    mut v_x_2119_: *mut LeanObject,
    mut v_x_2120_: *mut LeanObject,
    mut v_x_2121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9975__boxed_2122_: usize = 0;
    let mut v_res_2123_: *mut LeanObject = core::ptr::null_mut();
    v_x_9975__boxed_2122_ = lean_unbox_usize(v_x_2120_);
    lean_dec(v_x_2120_);
    v_res_2123_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1(v_00_u03b2_2118_, v_x_2119_, v_x_9975__boxed_2122_, v_x_2121_);
    lean_dec(v_x_2121_);
    lean_dec_ref(v_x_2119_);
    return v_res_2123_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(
    mut v_00_u03b2_2124_: *mut LeanObject,
    mut v_keys_2125_: *mut LeanObject,
    mut v_vals_2126_: *mut LeanObject,
    mut v_heq_2127_: *mut LeanObject,
    mut v_i_2128_: *mut LeanObject,
    mut v_k_2129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    v___x_2130_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___redArg(v_keys_2125_, v_vals_2126_, v_i_2128_, v_k_2129_);
    return v___x_2130_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_2131_: *mut LeanObject,
    mut v_keys_2132_: *mut LeanObject,
    mut v_vals_2133_: *mut LeanObject,
    mut v_heq_2134_: *mut LeanObject,
    mut v_i_2135_: *mut LeanObject,
    mut v_k_2136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2137_: *mut LeanObject = core::ptr::null_mut();
    v_res_2137_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn_spec__1_spec__1_spec__2(v_00_u03b2_2131_, v_keys_2132_, v_vals_2133_, v_heq_2134_, v_i_2135_, v_k_2136_);
    lean_dec(v_k_2136_);
    lean_dec_ref(v_vals_2133_);
    lean_dec_ref(v_keys_2132_);
    return v_res_2137_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(
    mut v_e_2143_: *mut LeanObject,
    mut v_a_2144_: *mut LeanObject,
    mut v_a_2145_: *mut LeanObject,
    mut v_a_2146_: *mut LeanObject,
    mut v_a_2147_: *mut LeanObject,
    mut v_a_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
    mut v_a_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
    mut v_a_2152_: *mut LeanObject,
    mut v_a_2153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: u8 = 0;
    let mut v_arg_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: u8 = 0;
    let mut v_arg_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: u8 = 0;
    let mut v_arg_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2199_: u8 = 0;
    let mut v___x_2200_: u8 = 0;
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2220_: u8 = 0;
    let mut v_a_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2224_: u8 = 0;
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2228_: u8 = 0;
    let mut v_isSharedCheck_2229_: u8 = 0;
    let mut v_a_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2233_: u8 = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_2143_);
                v___x_2158_ = l_Lean_Expr_cleanupAnnotations(v_e_2143_);
                v___x_2159_ = l_Lean_Expr_isApp(v___x_2158_);
                if v___x_2159_ == 0 {
                    lean_dec_ref(v___x_2158_);
                    lean_dec_ref(v_e_2143_);
                    state = 1;
                    continue;
                } else {
                    v_arg_2160_ = lean_ctor_get(v___x_2158_, 1);
                    lean_inc_ref(v_arg_2160_);
                    v___x_2161_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2158_);
                    v___x_2162_ = l_Lean_Expr_isApp(v___x_2161_);
                    if v___x_2162_ == 0 {
                        lean_dec_ref(v___x_2161_);
                        lean_dec_ref(v_arg_2160_);
                        lean_dec_ref(v_e_2143_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_2163_ = lean_ctor_get(v___x_2161_, 1);
                        lean_inc_ref(v_arg_2163_);
                        v___x_2164_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2161_);
                        v___x_2165_ = l_Lean_Expr_isApp(v___x_2164_);
                        if v___x_2165_ == 0 {
                            lean_dec_ref(v___x_2164_);
                            lean_dec_ref(v_arg_2163_);
                            lean_dec_ref(v_arg_2160_);
                            lean_dec_ref(v_e_2143_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_2166_ = lean_ctor_get(v___x_2164_, 1);
                            lean_inc_ref(v_arg_2166_);
                            v___x_2167_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2164_);
                            v___x_2193_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2;
                            v___x_2194_ = l_Lean_Expr_isConstOf(v___x_2167_, v___x_2193_);
                            if v___x_2194_ == 0 {
                                lean_dec_ref(v___x_2167_);
                                lean_dec_ref(v_arg_2166_);
                                lean_dec_ref(v_arg_2163_);
                                lean_dec_ref(v_arg_2160_);
                                lean_dec_ref(v_e_2143_);
                                state = 1;
                                continue;
                            } else {
                                lean_inc_ref(v_e_2143_);
                                v___x_2195_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                                    v_e_2143_, v_a_2144_, v_a_2148_, v_a_2150_, v_a_2151_,
                                    v_a_2152_, v_a_2153_,
                                );
                                if lean_obj_tag(v___x_2195_) == 0 {
                                    v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
                                    v_isSharedCheck_2229_ = (!lean_is_exclusive(v___x_2195_)) as u8;
                                    if v_isSharedCheck_2229_ == 0 {
                                        v___x_2198_ = v___x_2195_;
                                        v_isShared_2199_ = v_isSharedCheck_2229_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2196_);
                                        lean_dec(v___x_2195_);
                                        v___x_2198_ = lean_box(0);
                                        v_isShared_2199_ = v_isSharedCheck_2229_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v___x_2167_);
                                    lean_dec_ref(v_arg_2166_);
                                    lean_dec_ref(v_arg_2163_);
                                    lean_dec_ref(v_arg_2160_);
                                    lean_dec_ref(v_e_2143_);
                                    v_a_2230_ = lean_ctor_get(v___x_2195_, 0);
                                    v_isSharedCheck_2237_ = (!lean_is_exclusive(v___x_2195_)) as u8;
                                    if v_isSharedCheck_2237_ == 0 {
                                        v___x_2232_ = v___x_2195_;
                                        v_isShared_2233_ = v_isSharedCheck_2237_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2230_);
                                        lean_dec(v___x_2195_);
                                        v___x_2232_ = lean_box(0);
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
                v___x_2156_ = lean_box(0);
                v___x_2157_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2157_, 0, v___x_2156_);
                return v___x_2157_;
            }
            2 => {
                lean_inc_ref(v_e_2143_);
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
                if lean_obj_tag(v___x_2180_) == 0 {
                    v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
                    lean_inc(v_a_2181_);
                    lean_dec_ref_known(v___x_2180_, 1);
                    v___x_2182_ = l_Lean_Expr_constLevels_x21(v___x_2167_);
                    lean_dec_ref(v___x_2167_);
                    v___x_2183_ = l_Lean_Meta_mkOfEqTrueCore(v_e_2143_, v_a_2181_);
                    v___x_2184_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_initInjFn(v___x_2182_, v_arg_2166_, v_arg_2163_, v_f_2169_, v___x_2183_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
                    return v___x_2184_;
                } else {
                    lean_dec_ref(v_f_2169_);
                    lean_dec_ref(v___x_2167_);
                    lean_dec_ref(v_arg_2166_);
                    lean_dec_ref(v_arg_2163_);
                    lean_dec_ref(v_e_2143_);
                    v_a_2185_ = lean_ctor_get(v___x_2180_, 0);
                    v_isSharedCheck_2192_ = (!lean_is_exclusive(v___x_2180_)) as u8;
                    if v_isSharedCheck_2192_ == 0 {
                        v___x_2187_ = v___x_2180_;
                        v_isShared_2188_ = v_isSharedCheck_2192_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2185_);
                        lean_dec(v___x_2180_);
                        v___x_2187_ = lean_box(0);
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
                    v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
                    v___x_2190_ = v_reuseFailAlloc_2191_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2190_;
            }
            5 => {
                v___x_2200_ = (lean_unbox(v_a_2196_) as u8);
                lean_dec(v_a_2196_);
                if v___x_2200_ == 0 {
                    lean_dec_ref(v___x_2167_);
                    lean_dec_ref(v_arg_2166_);
                    lean_dec_ref(v_arg_2163_);
                    lean_dec_ref(v_arg_2160_);
                    lean_dec_ref(v_e_2143_);
                    v___x_2201_ = lean_box(0);
                    if v_isShared_2199_ == 0 {
                        lean_ctor_set(v___x_2198_, 0, v___x_2201_);
                        v___x_2203_ = v___x_2198_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
                        v___x_2203_ = v_reuseFailAlloc_2204_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2198_);
                    lean_inc_ref(v_arg_2160_);
                    v___x_2205_ = l_Lean_Expr_eta(v_arg_2160_);
                    v___x_2206_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_arg_2160_,
                            v___x_2205_,
                        );
                    if v___x_2206_ == 0 {
                        lean_dec_ref(v_arg_2160_);
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
                        if lean_obj_tag(v___x_2207_) == 0 {
                            v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
                            lean_inc(v_a_2208_);
                            lean_dec_ref_known(v___x_2207_, 1);
                            v___x_2209_ =
                                l_Lean_Meta_Grind_getGeneration___redArg(v_e_2143_, v_a_2144_);
                            if lean_obj_tag(v___x_2209_) == 0 {
                                v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
                                lean_inc(v_a_2210_);
                                lean_dec_ref_known(v___x_2209_, 1);
                                v___x_2211_ = lean_box(0);
                                lean_inc(v_a_2153_);
                                lean_inc_ref(v_a_2152_);
                                lean_inc(v_a_2151_);
                                lean_inc_ref(v_a_2150_);
                                lean_inc(v_a_2149_);
                                lean_inc_ref(v_a_2148_);
                                lean_inc(v_a_2147_);
                                lean_inc_ref(v_a_2146_);
                                lean_inc(v_a_2145_);
                                lean_inc(v_a_2144_);
                                lean_inc(v_a_2208_);
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
                                if lean_obj_tag(v___x_2212_) == 0 {
                                    lean_dec_ref_known(v___x_2212_, 1);
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
                                    lean_dec(v_a_2208_);
                                    lean_dec_ref(v___x_2167_);
                                    lean_dec_ref(v_arg_2166_);
                                    lean_dec_ref(v_arg_2163_);
                                    lean_dec_ref(v_e_2143_);
                                    return v___x_2212_;
                                }
                            } else {
                                lean_dec(v_a_2208_);
                                lean_dec_ref(v___x_2167_);
                                lean_dec_ref(v_arg_2166_);
                                lean_dec_ref(v_arg_2163_);
                                lean_dec_ref(v_e_2143_);
                                v_a_2213_ = lean_ctor_get(v___x_2209_, 0);
                                v_isSharedCheck_2220_ = (!lean_is_exclusive(v___x_2209_)) as u8;
                                if v_isSharedCheck_2220_ == 0 {
                                    v___x_2215_ = v___x_2209_;
                                    v_isShared_2216_ = v_isSharedCheck_2220_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2213_);
                                    lean_dec(v___x_2209_);
                                    v___x_2215_ = lean_box(0);
                                    v_isShared_2216_ = v_isSharedCheck_2220_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_2167_);
                            lean_dec_ref(v_arg_2166_);
                            lean_dec_ref(v_arg_2163_);
                            lean_dec_ref(v_e_2143_);
                            v_a_2221_ = lean_ctor_get(v___x_2207_, 0);
                            v_isSharedCheck_2228_ = (!lean_is_exclusive(v___x_2207_)) as u8;
                            if v_isSharedCheck_2228_ == 0 {
                                v___x_2223_ = v___x_2207_;
                                v_isShared_2224_ = v_isSharedCheck_2228_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_2221_);
                                lean_dec(v___x_2207_);
                                v___x_2223_ = lean_box(0);
                                v_isShared_2224_ = v_isSharedCheck_2228_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2205_);
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
                    v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
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
                    v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
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
                    v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
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
    mut v_e_2238_: *mut LeanObject,
    mut v_a_2239_: *mut LeanObject,
    mut v_a_2240_: *mut LeanObject,
    mut v_a_2241_: *mut LeanObject,
    mut v_a_2242_: *mut LeanObject,
    mut v_a_2243_: *mut LeanObject,
    mut v_a_2244_: *mut LeanObject,
    mut v_a_2245_: *mut LeanObject,
    mut v_a_2246_: *mut LeanObject,
    mut v_a_2247_: *mut LeanObject,
    mut v_a_2248_: *mut LeanObject,
    mut v_a_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2250_: *mut LeanObject = core::ptr::null_mut();
    v_res_2250_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj(
        v_e_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_,
        v_a_2246_, v_a_2247_, v_a_2248_,
    );
    lean_dec(v_a_2248_);
    lean_dec_ref(v_a_2247_);
    lean_dec(v_a_2246_);
    lean_dec_ref(v_a_2245_);
    lean_dec(v_a_2244_);
    lean_dec_ref(v_a_2243_);
    lean_dec(v_a_2242_);
    lean_dec_ref(v_a_2241_);
    lean_dec(v_a_2240_);
    lean_dec(v_a_2239_);
    return v_res_2250_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_()
-> *mut LeanObject {
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    v___x_2252_ =
        l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___closed__2;
    v___x_2253_ = lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___boxed
            as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_2254_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_2252_, v___x_2253_);
    return v___x_2254_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8____boxed(
    mut v_a_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2256_: *mut LeanObject = core::ptr::null_mut();
    v_res_2256_ = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_();
    return v_res_2256_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Propagator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Injective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj___regBuiltin___private_Lean_Meta_Tactic_Grind_PropagateInj_0__Lean_Meta_Grind_propagateInj_declare__1_00___x40_Lean_Meta_Tactic_Grind_PropagateInj_3930705876____hygCtx___hyg_8_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Propagator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Injective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
}
