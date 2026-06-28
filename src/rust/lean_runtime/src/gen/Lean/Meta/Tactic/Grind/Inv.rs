// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Inv
// Imports: Lean.Meta.Tactic.Grind.Types Init.Grind.Util Lean.Meta.Tactic.Grind.Util
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_PersistentArray_push___redArg,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_appFnCleanup___redArg,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_check;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types,
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash,
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent,
    l_Lean_Meta_Grind_ENode_isRoot, l_Lean_Meta_Grind_Goal_getENode,
    l_Lean_Meta_Grind_Goal_getEqcs, l_Lean_Meta_Grind_Goal_getNext, l_Lean_Meta_Grind_Goal_getRoot,
    l_Lean_Meta_Grind_Goal_getRoot_x3f, l_Lean_Meta_Grind_Goal_getTarget_x3f,
    l_Lean_Meta_Grind_ParentSet_elems, l_Lean_Meta_Grind_ParentSet_isEmpty,
    l_Lean_Meta_Grind_Solvers_checkInvariants, l_Lean_Meta_Grind_getCongrRoot___redArg,
    l_Lean_Meta_Grind_getExprs___redArg, l_Lean_Meta_Grind_getParents___redArg,
    l_Lean_Meta_Grind_grind_debug_proofs, l_Lean_Meta_Grind_hasSameType,
    l_Lean_Meta_Grind_instInhabitedGoalM, l_Lean_Meta_Grind_isCongrRoot___redArg,
    l_Lean_Meta_Grind_isRoot___redArg, l_Lean_Meta_Grind_mkEqHEqProof,
    l_Lean_Meta_Grind_updateLastTag, l_Lean_Meta_Grind_useFunCC___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Util::{
    initialize_Lean_Meta_Tactic_Grind_Util, l_Lean_Meta_Grind_isMatchCond,
    runtime_initialize_Lean_Meta_Tactic_Grind_Util,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_nat_sub, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_equal;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_10,
    lean_apply_11, lean_apply_12, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1: usize = 0;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1_value: LeanStringObject<63> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 99, 104, 101, 99, 107, 69, 113, 99, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2_value: LeanStringObject<75> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 75, m_capacity: 75, m_length: 74, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 110, 32, 114, 111, 111, 116, 46, 115, 101, 108, 102, 10, 32, 32, 32, 32, 45, 45, 32, 71, 111, 32, 116, 111, 32, 110, 101, 120, 116, 32, 101, 108, 101, 109, 101, 110, 116, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4_value: LeanStringObject<173> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 173, m_capacity: 173, m_length: 172, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 46, 54, 56, 52, 55, 55, 57, 54, 50, 57, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 50, 56, 50, 46, 48, 32, 41, 10, 32, 32, 32, 32, 45, 45, 32, 83, 116, 97, 114, 116, 105, 110, 103, 32, 97, 116, 32, 96, 99, 117, 114, 114, 96, 44, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 116, 104, 101, 32, 96, 116, 97, 114, 103, 101, 116, 63, 96, 32, 102, 105, 101, 108, 100, 32, 108, 101, 97, 100, 115, 32, 116, 111, 32, 96, 114, 111, 111, 116, 96, 46, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4_value) as *mut LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0_value: LeanStringObject<148> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 148, m_capacity: 148, m_length: 147, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 46, 54, 56, 52, 55, 55, 57, 54, 50, 57, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 53, 51, 46, 48, 32, 41, 32, 114, 111, 111, 116, 46, 115, 101, 108, 102, 10, 32, 32, 32, 32, 45, 45, 32, 67, 104, 101, 99, 107, 32, 99, 111, 110, 103, 114, 117, 101, 110, 99, 101, 32, 114, 111, 111, 116, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2_value: LeanStringObject<202> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 202, m_capacity: 202, m_length: 201, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 46, 54, 56, 52, 55, 55, 57, 54, 50, 57, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 50, 49, 57, 46, 48, 32, 41, 10, 32, 32, 32, 32, 45, 45, 32, 73, 102, 32, 116, 104, 101, 32, 101, 113, 117, 105, 118, 97, 108, 101, 110, 99, 101, 32, 99, 108, 97, 115, 115, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 72, 69, 113, 32, 112, 114, 111, 111, 102, 115, 44, 32, 116, 104, 101, 110, 32, 116, 104, 101, 32, 116, 121, 112, 101, 115, 32, 109, 117, 115, 116, 32, 98, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 46, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4_value: LeanStringObject<114> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 114, m_capacity: 114, m_length: 113, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 101, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 46, 54, 56, 52, 55, 55, 57, 54, 50, 57, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 49, 55, 50, 46, 48, 32, 41, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4_value) as *mut LeanObject;
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0_value:
    LeanStringObject<41> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 114, 111, 111, 116, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115, 105, 122, 101, 10,
        10, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [72, 69, 113, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__2_value) as *mut LeanObject,13589827700912665667 as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [77, 97, 116, 99, 104, 67, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__2_value) as *mut LeanObject,16774854854508800365 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3_value) as *mut LeanObject;
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0_value: LeanStringObject<67> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 99, 104, 101, 99, 107, 80, 97, 114, 101, 110, 116, 115, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1_value: LeanStringObject<102> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 102, m_capacity: 102, m_length: 101, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 46, 51, 49, 52, 53, 54, 52, 53, 56, 48, 56, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 49, 57, 51, 46, 48, 32, 41, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3_value: LeanStringObject<100> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 100, m_capacity: 100, m_length: 99, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 46, 51, 49, 52, 53, 54, 52, 53, 56, 48, 56, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 52, 56, 56, 46, 48, 32, 41, 10, 32, 32, 32, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [101, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [44, 32, 112, 97, 114, 101, 110, 116, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0_value: LeanStringObject<105> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 105, m_capacity: 105, m_length: 104, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 46, 51, 49, 52, 53, 54, 52, 53, 56, 48, 56, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 53, 51, 50, 46, 48, 32, 41, 46, 105, 115, 69, 109, 112, 116, 121, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0_value: LeanStringObject<80> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 80, m_capacity: 80, m_length: 79, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 99, 104, 101, 99, 107, 80, 116, 114, 69, 113, 73, 109, 112, 108, 105, 101, 115, 83, 116, 114, 117, 99, 116, 69, 113, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1_value: LeanStringObject<45> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 40, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 33, 69, 120, 112, 114, 46, 101, 113, 117, 97, 108, 32, 101, 226, 130, 129, 32, 101, 226, 130, 130, 10, 10, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3_value: LeanStringObject<114> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 114, m_capacity: 114, m_length: 109, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 33, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 101, 226, 130, 129, 32, 101, 226, 130, 130, 10, 32, 32, 32, 32, 32, 32, 45, 45, 32, 97, 110, 100, 32, 116, 104, 101, 32, 116, 119, 111, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 115, 32, 109, 117, 115, 116, 32, 110, 111, 116, 32, 98, 101, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 114, 111, 111, 102, 115, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2_value) as *mut LeanObject;
static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__0_value) as *mut LeanObject,15947788021050471391 as *mut LeanObject] };
static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__1_value) as *mut LeanObject,5637236024813792860 as *mut LeanObject] };
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__2_value) as *mut LeanObject,1833026388428387609 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__4_value) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__4_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [99, 104, 101, 99, 107, 101, 100, 58, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 61, 32, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    v___x_2940_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_2940_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(
    mut v_msg_2941_: *mut LeanObject,
    mut v___y_2942_: *mut LeanObject,
    mut v___y_2943_: *mut LeanObject,
    mut v___y_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
    mut v___y_2950_: *mut LeanObject,
    mut v___y_2951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_30751__overap_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    v___x_2953_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___closed__0);
    v___x_30751__overap_2954_ = lean_panic_fn_borrowed(v___x_2953_, v_msg_2941_);
    lean_inc(v___y_2951_);
    lean_inc_ref(v___y_2950_);
    lean_inc(v___y_2949_);
    lean_inc_ref(v___y_2948_);
    lean_inc(v___y_2947_);
    lean_inc_ref(v___y_2946_);
    lean_inc(v___y_2945_);
    lean_inc_ref(v___y_2944_);
    lean_inc(v___y_2943_);
    lean_inc(v___y_2942_);
    v___x_2955_ = lean_apply_11(
        v___x_30751__overap_2954_,
        v___y_2942_,
        v___y_2943_,
        v___y_2944_,
        v___y_2945_,
        v___y_2946_,
        v___y_2947_,
        v___y_2948_,
        v___y_2949_,
        v___y_2950_,
        v___y_2951_,
        lean_box(0),
    );
    return v___x_2955_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0___boxed(
    mut v_msg_2956_: *mut LeanObject,
    mut v___y_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
    mut v___y_2959_: *mut LeanObject,
    mut v___y_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
    mut v___y_2965_: *mut LeanObject,
    mut v___y_2966_: *mut LeanObject,
    mut v___y_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2968_: *mut LeanObject = core::ptr::null_mut();
    v_res_2968_ =
        l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(
            v_msg_2956_,
            v___y_2957_,
            v___y_2958_,
            v___y_2959_,
            v___y_2960_,
            v___y_2961_,
            v___y_2962_,
            v___y_2963_,
            v___y_2964_,
            v___y_2965_,
            v___y_2966_,
        );
    lean_dec(v___y_2966_);
    lean_dec_ref(v___y_2965_);
    lean_dec(v___y_2964_);
    lean_dec_ref(v___y_2963_);
    lean_dec(v___y_2962_);
    lean_dec_ref(v___y_2961_);
    lean_dec(v___y_2960_);
    lean_dec_ref(v___y_2959_);
    lean_dec(v___y_2958_);
    lean_dec(v___y_2957_);
    return v_res_2968_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    v___x_2969_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_2969_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(
    mut v_msg_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
    mut v___y_2972_: *mut LeanObject,
    mut v___y_2973_: *mut LeanObject,
    mut v___y_2974_: *mut LeanObject,
    mut v___y_2975_: *mut LeanObject,
    mut v___y_2976_: *mut LeanObject,
    mut v___y_2977_: *mut LeanObject,
    mut v___y_2978_: *mut LeanObject,
    mut v___y_2979_: *mut LeanObject,
    mut v___y_2980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_32428__overap_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    v___x_2982_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___closed__0);
    v___x_32428__overap_2983_ = lean_panic_fn_borrowed(v___x_2982_, v_msg_2970_);
    lean_inc(v___y_2980_);
    lean_inc_ref(v___y_2979_);
    lean_inc(v___y_2978_);
    lean_inc_ref(v___y_2977_);
    lean_inc(v___y_2976_);
    lean_inc_ref(v___y_2975_);
    lean_inc(v___y_2974_);
    lean_inc_ref(v___y_2973_);
    lean_inc(v___y_2972_);
    lean_inc(v___y_2971_);
    v___x_2984_ = lean_apply_11(
        v___x_32428__overap_2983_,
        v___y_2971_,
        v___y_2972_,
        v___y_2973_,
        v___y_2974_,
        v___y_2975_,
        v___y_2976_,
        v___y_2977_,
        v___y_2978_,
        v___y_2979_,
        v___y_2980_,
        lean_box(0),
    );
    return v___x_2984_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4___boxed(
    mut v_msg_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
    mut v___y_2991_: *mut LeanObject,
    mut v___y_2992_: *mut LeanObject,
    mut v___y_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
    mut v___y_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2997_: *mut LeanObject = core::ptr::null_mut();
    v_res_2997_ =
        l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(
            v_msg_2985_,
            v___y_2986_,
            v___y_2987_,
            v___y_2988_,
            v___y_2989_,
            v___y_2990_,
            v___y_2991_,
            v___y_2992_,
            v___y_2993_,
            v___y_2994_,
            v___y_2995_,
        );
    lean_dec(v___y_2995_);
    lean_dec_ref(v___y_2994_);
    lean_dec(v___y_2993_);
    lean_dec_ref(v___y_2992_);
    lean_dec(v___y_2991_);
    lean_dec_ref(v___y_2990_);
    lean_dec(v___y_2989_);
    lean_dec_ref(v___y_2988_);
    lean_dec(v___y_2987_);
    lean_dec(v___y_2986_);
    return v_res_2997_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(
    mut v___x_2998_: *mut LeanObject,
    mut v_keys_2999_: *mut LeanObject,
    mut v_vals_3000_: *mut LeanObject,
    mut v_i_3001_: *mut LeanObject,
    mut v_k_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: u8 = 0;
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u8 = 0;
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3003_ = lean_array_get_size(v_keys_2999_);
                v___x_3004_ = lean_nat_dec_lt(v_i_3001_, v___x_3003_);
                if v___x_3004_ == 0 {
                    lean_dec_ref(v_k_3002_);
                    lean_dec(v_i_3001_);
                    v___x_3005_ = lean_box(0);
                    return v___x_3005_;
                } else {
                    v_k_x27_3006_ = lean_array_fget_borrowed(v_keys_2999_, v_i_3001_);
                    lean_inc(v_k_x27_3006_);
                    lean_inc_ref(v_k_3002_);
                    v___x_3007_ =
                        l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(
                            v___x_2998_,
                            v_k_3002_,
                            v_k_x27_3006_,
                        );
                    if v___x_3007_ == 0 {
                        v___x_3008_ = lean_unsigned_to_nat(1);
                        v___x_3009_ = lean_nat_add(v_i_3001_, v___x_3008_);
                        lean_dec(v_i_3001_);
                        v_i_3001_ = v___x_3009_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_3002_);
                        v___x_3011_ = lean_array_fget_borrowed(v_vals_3000_, v_i_3001_);
                        lean_dec(v_i_3001_);
                        lean_inc(v___x_3011_);
                        lean_inc(v_k_x27_3006_);
                        v___x_3012_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3012_, 0, v_k_x27_3006_);
                        lean_ctor_set(v___x_3012_, 1, v___x_3011_);
                        v___x_3013_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3013_, 0, v___x_3012_);
                        return v___x_3013_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg___boxed(
    mut v___x_3014_: *mut LeanObject,
    mut v_keys_3015_: *mut LeanObject,
    mut v_vals_3016_: *mut LeanObject,
    mut v_i_3017_: *mut LeanObject,
    mut v_k_3018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3019_: *mut LeanObject = core::ptr::null_mut();
    v_res_3019_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_3014_, v_keys_3015_, v_vals_3016_, v_i_3017_, v_k_3018_);
    lean_dec_ref(v_vals_3016_);
    lean_dec_ref(v_keys_3015_);
    lean_dec_ref(v___x_3014_);
    return v_res_3019_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_3020_: usize = 0;
    let mut v___x_3021_: usize = 0;
    let mut v___x_3022_: usize = 0;
    v___x_3020_ = 5usize;
    v___x_3021_ = 1usize;
    v___x_3022_ = lean_usize_shift_left(v___x_3021_, v___x_3020_);
    return v___x_3022_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_3023_: usize = 0;
    let mut v___x_3024_: usize = 0;
    let mut v___x_3025_: usize = 0;
    v___x_3023_ = 1usize;
    v___x_3024_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__0);
    v___x_3025_ = lean_usize_sub(v___x_3024_, v___x_3023_);
    return v___x_3025_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(
    mut v___x_3026_: *mut LeanObject,
    mut v_x_3027_: *mut LeanObject,
    mut v_x_3028_: usize,
    mut v_x_3029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: usize = 0;
    let mut v___x_3033_: usize = 0;
    let mut v___x_3034_: usize = 0;
    let mut v_j_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: usize = 0;
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3027_) == 0 {
                    v_es_3030_ = lean_ctor_get(v_x_3027_, 0);
                    lean_inc_ref(v_es_3030_);
                    lean_dec_ref_known(v_x_3027_, 1);
                    v___x_3031_ = lean_box(2);
                    v___x_3032_ = 5usize;
                    v___x_3033_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___closed__1);
                    v___x_3034_ = lean_usize_land(v_x_3028_, v___x_3033_);
                    v_j_3035_ = lean_usize_to_nat(v___x_3034_);
                    v___x_3036_ = lean_array_get(v___x_3031_, v_es_3030_, v_j_3035_);
                    lean_dec(v_j_3035_);
                    lean_dec_ref(v_es_3030_);
                    match lean_obj_tag(v___x_3036_) {
                        0 => {
                            v_key_3037_ = lean_ctor_get(v___x_3036_, 0);
                            lean_inc_n(v_key_3037_, 2);
                            v_val_3038_ = lean_ctor_get(v___x_3036_, 1);
                            lean_inc(v_val_3038_);
                            lean_dec_ref_known(v___x_3036_, 2);
                            v___x_3039_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_3026_, v_x_3029_, v_key_3037_);
                            if v___x_3039_ == 0 {
                                lean_dec(v_val_3038_);
                                lean_dec(v_key_3037_);
                                v___x_3040_ = lean_box(0);
                                return v___x_3040_;
                            } else {
                                v___x_3041_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3041_, 0, v_key_3037_);
                                lean_ctor_set(v___x_3041_, 1, v_val_3038_);
                                v___x_3042_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3042_, 0, v___x_3041_);
                                return v___x_3042_;
                            }
                        }
                        1 => {
                            v_node_3043_ = lean_ctor_get(v___x_3036_, 0);
                            lean_inc(v_node_3043_);
                            lean_dec_ref_known(v___x_3036_, 1);
                            v___x_3044_ = lean_usize_shift_right(v_x_3028_, v___x_3032_);
                            v_x_3027_ = v_node_3043_;
                            v_x_3028_ = v___x_3044_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            lean_dec_ref(v_x_3029_);
                            v___x_3046_ = lean_box(0);
                            return v___x_3046_;
                        }
                    }
                } else {
                    v_ks_3047_ = lean_ctor_get(v_x_3027_, 0);
                    lean_inc_ref(v_ks_3047_);
                    v_vs_3048_ = lean_ctor_get(v_x_3027_, 1);
                    lean_inc_ref(v_vs_3048_);
                    lean_dec_ref_known(v_x_3027_, 2);
                    v___x_3049_ = lean_unsigned_to_nat(0);
                    v___x_3050_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_3026_, v_ks_3047_, v_vs_3048_, v___x_3049_, v_x_3029_);
                    lean_dec_ref(v_vs_3048_);
                    lean_dec_ref(v_ks_3047_);
                    return v___x_3050_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg___boxed(
    mut v___x_3051_: *mut LeanObject,
    mut v_x_3052_: *mut LeanObject,
    mut v_x_3053_: *mut LeanObject,
    mut v_x_3054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_32977__boxed_3055_: usize = 0;
    let mut v_res_3056_: *mut LeanObject = core::ptr::null_mut();
    v_x_32977__boxed_3055_ = lean_unbox_usize(v_x_3053_);
    lean_dec(v_x_3053_);
    v_res_3056_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_3051_, v_x_3052_, v_x_32977__boxed_3055_, v_x_3054_);
    lean_dec_ref(v___x_3051_);
    return v_res_3056_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(
    mut v___x_3057_: *mut LeanObject,
    mut v_x_3058_: *mut LeanObject,
    mut v_x_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3060_: u64 = 0;
    let mut v___x_3061_: usize = 0;
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_x_3059_);
    v___x_3060_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(
        v___x_3057_,
        v_x_3059_,
    );
    v___x_3061_ = lean_uint64_to_usize(v___x_3060_);
    lean_inc_ref(v_x_3058_);
    v___x_3062_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_3057_, v_x_3058_, v___x_3061_, v_x_3059_);
    return v___x_3062_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg___boxed(
    mut v___x_3063_: *mut LeanObject,
    mut v_x_3064_: *mut LeanObject,
    mut v_x_3065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3066_: *mut LeanObject = core::ptr::null_mut();
    v_res_3066_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_3063_, v_x_3064_, v_x_3065_);
    lean_dec_ref(v_x_3064_);
    lean_dec_ref(v___x_3063_);
    return v_res_3066_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(
    mut v_a_3067_: *mut LeanObject,
    mut v___y_3068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3070_ = lean_st_ref_get(v___y_3068_);
                v___x_3071_ = l_Lean_Meta_Grind_Goal_getTarget_x3f(v___x_3070_, v_a_3067_);
                lean_dec(v___x_3070_);
                if lean_obj_tag(v___x_3071_) == 1 {
                    lean_dec_ref(v_a_3067_);
                    v_val_3072_ = lean_ctor_get(v___x_3071_, 0);
                    lean_inc(v_val_3072_);
                    lean_dec_ref_known(v___x_3071_, 1);
                    v_a_3067_ = v_val_3072_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___x_3071_);
                    v___x_3074_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3074_, 0, v_a_3067_);
                    return v___x_3074_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg___boxed(
    mut v_a_3075_: *mut LeanObject,
    mut v___y_3076_: *mut LeanObject,
    mut v___y_3077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3078_: *mut LeanObject = core::ptr::null_mut();
    v_res_3078_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_a_3075_, v___y_3076_);
    lean_dec(v___y_3076_);
    return v_res_3078_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    v___x_3082_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__2;
    v___x_3083_ = lean_unsigned_to_nat(4);
    v___x_3084_ = lean_unsigned_to_nat(40);
    v___x_3085_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1;
    v___x_3086_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_3087_ = l_mkPanicMessageWithDecl(
        v___x_3086_,
        v___x_3085_,
        v___x_3084_,
        v___x_3083_,
        v___x_3082_,
    );
    return v___x_3087_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    v___x_3089_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__4;
    v___x_3090_ = lean_unsigned_to_nat(6);
    v___x_3091_ = lean_unsigned_to_nat(32);
    v___x_3092_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1;
    v___x_3093_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_3094_ = l_mkPanicMessageWithDecl(
        v___x_3093_,
        v___x_3092_,
        v___x_3091_,
        v___x_3090_,
        v___x_3089_,
    );
    return v___x_3094_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(
    mut v_root_3095_: *mut LeanObject,
    mut v_snd_3096_: *mut LeanObject,
    mut v_curr_3097_: *mut LeanObject,
    mut v___x_3098_: *mut LeanObject,
    mut v_____r_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
    mut v___y_3101_: *mut LeanObject,
    mut v___y_3102_: *mut LeanObject,
    mut v___y_3103_: *mut LeanObject,
    mut v___y_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
    mut v___y_3109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3132_: u8 = 0;
    let mut v___x_3133_: u8 = 0;
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3144_: u8 = 0;
    let mut v_a_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3152_: u8 = 0;
    let mut v_a_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut v_heqProofs_3161_: u8 = 0;
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: u8 = 0;
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3170_: u8 = 0;
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_heqProofs_3161_ = lean_ctor_get_uint8(
                    v_root_3095_,
                    (core::mem::size_of::<*mut LeanObject>() * 12 + 4) as u32,
                );
                if v_heqProofs_3161_ == 0 {
                    lean_inc_ref(v_curr_3097_);
                    lean_inc(v_snd_3096_);
                    v___x_3162_ = l_Lean_Meta_Grind_hasSameType(
                        v_snd_3096_,
                        v_curr_3097_,
                        v___y_3106_,
                        v___y_3107_,
                        v___y_3108_,
                        v___y_3109_,
                    );
                    if lean_obj_tag(v___x_3162_) == 0 {
                        v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
                        lean_inc(v_a_3163_);
                        lean_dec_ref_known(v___x_3162_, 1);
                        v___x_3164_ = (lean_unbox(v_a_3163_) as u8);
                        lean_dec(v_a_3163_);
                        if v___x_3164_ == 0 {
                            lean_dec(v___x_3098_);
                            lean_dec_ref(v_curr_3097_);
                            lean_dec(v_snd_3096_);
                            v___x_3165_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__5);
                            v___x_3166_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_3165_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
                            return v___x_3166_;
                        } else {
                            v___y_3112_ = v___y_3100_;
                            v___y_3113_ = v___y_3101_;
                            v___y_3114_ = v___y_3102_;
                            v___y_3115_ = v___y_3103_;
                            v___y_3116_ = v___y_3104_;
                            v___y_3117_ = v___y_3105_;
                            v___y_3118_ = v___y_3106_;
                            v___y_3119_ = v___y_3107_;
                            v___y_3120_ = v___y_3108_;
                            v___y_3121_ = v___y_3109_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3098_);
                        lean_dec_ref(v_curr_3097_);
                        lean_dec(v_snd_3096_);
                        v_a_3167_ = lean_ctor_get(v___x_3162_, 0);
                        v_isSharedCheck_3174_ = (!lean_is_exclusive(v___x_3162_)) as u8;
                        if v_isSharedCheck_3174_ == 0 {
                            v___x_3169_ = v___x_3162_;
                            v_isShared_3170_ = v_isSharedCheck_3174_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3167_);
                            lean_dec(v___x_3162_);
                            v___x_3169_ = lean_box(0);
                            v_isShared_3170_ = v_isSharedCheck_3174_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    v___y_3112_ = v___y_3100_;
                    v___y_3113_ = v___y_3101_;
                    v___y_3114_ = v___y_3102_;
                    v___y_3115_ = v___y_3103_;
                    v___y_3116_ = v___y_3104_;
                    v___y_3117_ = v___y_3105_;
                    v___y_3118_ = v___y_3106_;
                    v___y_3119_ = v___y_3107_;
                    v___y_3120_ = v___y_3108_;
                    v___y_3121_ = v___y_3109_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_snd_3096_);
                v___x_3122_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_snd_3096_, v___y_3112_);
                if lean_obj_tag(v___x_3122_) == 0 {
                    v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
                    lean_inc(v_a_3123_);
                    lean_dec_ref_known(v___x_3122_, 1);
                    v___x_3124_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_a_3123_,
                            v_curr_3097_,
                        );
                    lean_dec(v_a_3123_);
                    if v___x_3124_ == 0 {
                        lean_dec(v___x_3098_);
                        lean_dec_ref(v_curr_3097_);
                        lean_dec(v_snd_3096_);
                        v___x_3125_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__3);
                        v___x_3126_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_3125_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
                        return v___x_3126_;
                    } else {
                        v___x_3127_ = lean_st_ref_get(v___y_3112_);
                        v___x_3128_ = l_Lean_Meta_Grind_Goal_getNext(
                            v___x_3127_,
                            v_snd_3096_,
                            v___y_3118_,
                            v___y_3119_,
                            v___y_3120_,
                            v___y_3121_,
                        );
                        lean_dec(v___x_3127_);
                        if lean_obj_tag(v___x_3128_) == 0 {
                            v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
                            v_isSharedCheck_3144_ = (!lean_is_exclusive(v___x_3128_)) as u8;
                            if v_isSharedCheck_3144_ == 0 {
                                v___x_3131_ = v___x_3128_;
                                v_isShared_3132_ = v_isSharedCheck_3144_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3129_);
                                lean_dec(v___x_3128_);
                                v___x_3131_ = lean_box(0);
                                v_isShared_3132_ = v_isSharedCheck_3144_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3098_);
                            lean_dec_ref(v_curr_3097_);
                            v_a_3145_ = lean_ctor_get(v___x_3128_, 0);
                            v_isSharedCheck_3152_ = (!lean_is_exclusive(v___x_3128_)) as u8;
                            if v_isSharedCheck_3152_ == 0 {
                                v___x_3147_ = v___x_3128_;
                                v_isShared_3148_ = v_isSharedCheck_3152_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3145_);
                                lean_dec(v___x_3128_);
                                v___x_3147_ = lean_box(0);
                                v_isShared_3148_ = v_isSharedCheck_3152_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___x_3098_);
                    lean_dec_ref(v_curr_3097_);
                    lean_dec(v_snd_3096_);
                    v_a_3153_ = lean_ctor_get(v___x_3122_, 0);
                    v_isSharedCheck_3160_ = (!lean_is_exclusive(v___x_3122_)) as u8;
                    if v_isSharedCheck_3160_ == 0 {
                        v___x_3155_ = v___x_3122_;
                        v_isShared_3156_ = v_isSharedCheck_3160_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3153_);
                        lean_dec(v___x_3122_);
                        v___x_3155_ = lean_box(0);
                        v_isShared_3156_ = v_isSharedCheck_3160_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3133_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_curr_3097_,
                        v_a_3129_,
                    );
                lean_dec_ref(v_curr_3097_);
                if v___x_3133_ == 0 {
                    v___x_3134_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3134_, 0, v___x_3098_);
                    lean_ctor_set(v___x_3134_, 1, v_a_3129_);
                    v___x_3135_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3135_, 0, v___x_3134_);
                    if v_isShared_3132_ == 0 {
                        lean_ctor_set(v___x_3131_, 0, v___x_3135_);
                        v___x_3137_ = v___x_3131_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
                        v___x_3137_ = v_reuseFailAlloc_3138_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_3139_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3139_, 0, v___x_3098_);
                    lean_ctor_set(v___x_3139_, 1, v_a_3129_);
                    v___x_3140_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3140_, 0, v___x_3139_);
                    if v_isShared_3132_ == 0 {
                        lean_ctor_set(v___x_3131_, 0, v___x_3140_);
                        v___x_3142_ = v___x_3131_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
                        v___x_3142_ = v_reuseFailAlloc_3143_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3137_;
            }
            4 => {
                return v___x_3142_;
            }
            5 => {
                if v_isShared_3148_ == 0 {
                    v___x_3150_ = v___x_3147_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
                    v___x_3150_ = v_reuseFailAlloc_3151_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3150_;
            }
            7 => {
                if v_isShared_3156_ == 0 {
                    v___x_3158_ = v___x_3155_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
                    v___x_3158_ = v_reuseFailAlloc_3159_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3158_;
            }
            9 => {
                if v_isShared_3170_ == 0 {
                    v___x_3172_ = v___x_3169_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
                    v___x_3172_ = v_reuseFailAlloc_3173_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3172_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___boxed(
    mut v_root_3175_: *mut LeanObject,
    mut v_snd_3176_: *mut LeanObject,
    mut v_curr_3177_: *mut LeanObject,
    mut v___x_3178_: *mut LeanObject,
    mut v_____r_3179_: *mut LeanObject,
    mut v___y_3180_: *mut LeanObject,
    mut v___y_3181_: *mut LeanObject,
    mut v___y_3182_: *mut LeanObject,
    mut v___y_3183_: *mut LeanObject,
    mut v___y_3184_: *mut LeanObject,
    mut v___y_3185_: *mut LeanObject,
    mut v___y_3186_: *mut LeanObject,
    mut v___y_3187_: *mut LeanObject,
    mut v___y_3188_: *mut LeanObject,
    mut v___y_3189_: *mut LeanObject,
    mut v___y_3190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3191_: *mut LeanObject = core::ptr::null_mut();
    v_res_3191_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_3175_, v_snd_3176_, v_curr_3177_, v___x_3178_, v_____r_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
    lean_dec(v___y_3189_);
    lean_dec_ref(v___y_3188_);
    lean_dec(v___y_3187_);
    lean_dec_ref(v___y_3186_);
    lean_dec(v___y_3185_);
    lean_dec_ref(v___y_3184_);
    lean_dec(v___y_3183_);
    lean_dec_ref(v___y_3182_);
    lean_dec(v___y_3181_);
    lean_dec(v___y_3180_);
    lean_dec_ref(v_root_3175_);
    return v_res_3191_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    v___x_3193_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__0;
    v___x_3194_ = lean_unsigned_to_nat(4);
    v___x_3195_ = lean_unsigned_to_nat(22);
    v___x_3196_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1;
    v___x_3197_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_3198_ = l_mkPanicMessageWithDecl(
        v___x_3197_,
        v___x_3196_,
        v___x_3195_,
        v___x_3194_,
        v___x_3193_,
    );
    return v___x_3198_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    v___x_3200_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__2;
    v___x_3201_ = lean_unsigned_to_nat(8);
    v___x_3202_ = lean_unsigned_to_nat(29);
    v___x_3203_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1;
    v___x_3204_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_3205_ = l_mkPanicMessageWithDecl(
        v___x_3204_,
        v___x_3203_,
        v___x_3202_,
        v___x_3201_,
        v___x_3200_,
    );
    return v___x_3205_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    v___x_3207_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__4;
    v___x_3208_ = lean_unsigned_to_nat(10);
    v___x_3209_ = lean_unsigned_to_nat(27);
    v___x_3210_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1;
    v___x_3211_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_3212_ = l_mkPanicMessageWithDecl(
        v___x_3211_,
        v___x_3210_,
        v___x_3209_,
        v___x_3208_,
        v___x_3207_,
    );
    return v___x_3212_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(
    mut v_curr_3213_: *mut LeanObject,
    mut v_root_3214_: *mut LeanObject,
    mut v_a_3215_: *mut LeanObject,
    mut v___y_3216_: *mut LeanObject,
    mut v___y_3217_: *mut LeanObject,
    mut v___y_3218_: *mut LeanObject,
    mut v___y_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
    mut v___y_3222_: *mut LeanObject,
    mut v___y_3223_: *mut LeanObject,
    mut v___y_3224_: *mut LeanObject,
    mut v___y_3225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3232_: u8 = 0;
    let mut v_a_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v_a_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: u8 = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrTable_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: u8 = 0;
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3280_: u8 = 0;
    let mut v_val_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: u8 = 0;
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: u8 = 0;
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3300_: u8 = 0;
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v_a_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3308_: u8 = 0;
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3312_: u8 = 0;
    let mut v_a_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3316_: u8 = 0;
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3248_ = lean_st_ref_get(v___y_3216_);
                v_fst_3249_ = lean_ctor_get(v_a_3215_, 0);
                lean_inc(v_fst_3249_);
                v_snd_3250_ = lean_ctor_get(v_a_3215_, 1);
                lean_inc_n(v_snd_3250_, 2);
                lean_dec_ref(v_a_3215_);
                v___x_3251_ = l_Lean_Meta_Grind_Goal_getRoot(
                    v___x_3248_,
                    v_snd_3250_,
                    v___y_3222_,
                    v___y_3223_,
                    v___y_3224_,
                    v___y_3225_,
                );
                lean_dec(v___x_3248_);
                if lean_obj_tag(v___x_3251_) == 0 {
                    v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
                    lean_inc(v_a_3252_);
                    lean_dec_ref_known(v___x_3251_, 1);
                    v___x_3253_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_a_3252_,
                            v_curr_3213_,
                        );
                    lean_dec(v_a_3252_);
                    if v___x_3253_ == 0 {
                        lean_dec(v_snd_3250_);
                        lean_dec(v_fst_3249_);
                        v___x_3254_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__1);
                        v___x_3255_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_3254_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
                        v___y_3228_ = v___x_3255_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3256_ = lean_unsigned_to_nat(1);
                        v___x_3257_ = lean_nat_add(v_fst_3249_, v___x_3256_);
                        lean_dec(v_fst_3249_);
                        v___x_3258_ = l_Lean_Expr_isApp(v_snd_3250_);
                        if v___x_3258_ == 0 {
                            v___x_3259_ = lean_box(0);
                            lean_inc_ref(v_curr_3213_);
                            v___x_3260_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_3214_, v_snd_3250_, v_curr_3213_, v___x_3257_, v___x_3259_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
                            v___y_3228_ = v___x_3260_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3261_ = lean_st_ref_get(v___y_3216_);
                            v_toGoalState_3262_ = lean_ctor_get(v___x_3261_, 0);
                            lean_inc_ref(v_toGoalState_3262_);
                            lean_dec(v___x_3261_);
                            v_enodeMap_3263_ = lean_ctor_get(v_toGoalState_3262_, 1);
                            lean_inc_ref(v_enodeMap_3263_);
                            v_congrTable_3264_ = lean_ctor_get(v_toGoalState_3262_, 4);
                            lean_inc_ref(v_congrTable_3264_);
                            lean_dec_ref(v_toGoalState_3262_);
                            lean_inc(v_snd_3250_);
                            v___x_3265_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v_enodeMap_3263_, v_congrTable_3264_, v_snd_3250_);
                            lean_dec_ref(v_congrTable_3264_);
                            lean_dec_ref(v_enodeMap_3263_);
                            if lean_obj_tag(v___x_3265_) == 0 {
                                lean_inc(v_snd_3250_);
                                v___x_3266_ = l_Lean_Meta_Grind_isCongrRoot___redArg(
                                    v_snd_3250_,
                                    v___y_3216_,
                                    v___y_3222_,
                                    v___y_3223_,
                                    v___y_3224_,
                                    v___y_3225_,
                                );
                                if lean_obj_tag(v___x_3266_) == 0 {
                                    v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
                                    lean_inc(v_a_3267_);
                                    lean_dec_ref_known(v___x_3266_, 1);
                                    v___x_3268_ = (lean_unbox(v_a_3267_) as u8);
                                    lean_dec(v_a_3267_);
                                    if v___x_3268_ == 0 {
                                        lean_dec(v___x_3257_);
                                        lean_dec(v_snd_3250_);
                                        v___x_3269_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__3);
                                        v___x_3270_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_3269_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
                                        v___y_3228_ = v___x_3270_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3271_ = lean_box(0);
                                        lean_inc_ref(v_curr_3213_);
                                        v___x_3272_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_3214_, v_snd_3250_, v_curr_3213_, v___x_3257_, v___x_3271_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
                                        v___y_3228_ = v___x_3272_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_3257_);
                                    lean_dec(v_snd_3250_);
                                    lean_dec_ref(v_curr_3213_);
                                    v_a_3273_ = lean_ctor_get(v___x_3266_, 0);
                                    v_isSharedCheck_3280_ = (!lean_is_exclusive(v___x_3266_)) as u8;
                                    if v_isSharedCheck_3280_ == 0 {
                                        v___x_3275_ = v___x_3266_;
                                        v_isShared_3276_ = v_isSharedCheck_3280_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3273_);
                                        lean_dec(v___x_3266_);
                                        v___x_3275_ = lean_box(0);
                                        v_isShared_3276_ = v_isSharedCheck_3280_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                v_val_3281_ = lean_ctor_get(v___x_3265_, 0);
                                lean_inc(v_val_3281_);
                                lean_dec_ref_known(v___x_3265_, 1);
                                v_fst_3282_ = lean_ctor_get(v_val_3281_, 0);
                                lean_inc(v_fst_3282_);
                                lean_dec(v_val_3281_);
                                v___x_3283_ = l_Lean_Expr_getAppFn(v_fst_3282_);
                                v___x_3284_ = l_Lean_Expr_getAppFn(v_snd_3250_);
                                v___x_3285_ = l_Lean_Meta_Grind_hasSameType(
                                    v___x_3283_,
                                    v___x_3284_,
                                    v___y_3222_,
                                    v___y_3223_,
                                    v___y_3224_,
                                    v___y_3225_,
                                );
                                if lean_obj_tag(v___x_3285_) == 0 {
                                    v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
                                    lean_inc(v_a_3286_);
                                    lean_dec_ref_known(v___x_3285_, 1);
                                    v___x_3287_ = (lean_unbox(v_a_3286_) as u8);
                                    lean_dec(v_a_3286_);
                                    if v___x_3287_ == 0 {
                                        lean_dec(v_fst_3282_);
                                        v___x_3288_ = lean_box(0);
                                        lean_inc_ref(v_curr_3213_);
                                        v___x_3289_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_3214_, v_snd_3250_, v_curr_3213_, v___x_3257_, v___x_3288_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
                                        v___y_3228_ = v___x_3289_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_snd_3250_);
                                        v___x_3290_ = l_Lean_Meta_Grind_getCongrRoot___redArg(
                                            v_snd_3250_,
                                            v___y_3216_,
                                            v___y_3222_,
                                            v___y_3223_,
                                            v___y_3224_,
                                            v___y_3225_,
                                        );
                                        if lean_obj_tag(v___x_3290_) == 0 {
                                            v_a_3291_ = lean_ctor_get(v___x_3290_, 0);
                                            lean_inc(v_a_3291_);
                                            lean_dec_ref_known(v___x_3290_, 1);
                                            v___x_3292_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_3282_, v_a_3291_);
                                            lean_dec(v_a_3291_);
                                            lean_dec(v_fst_3282_);
                                            if v___x_3292_ == 0 {
                                                lean_dec(v___x_3257_);
                                                lean_dec(v_snd_3250_);
                                                v___x_3293_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5_once), _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___closed__5);
                                                v___x_3294_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__0(v___x_3293_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
                                                v___y_3228_ = v___x_3294_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_3295_ = lean_box(0);
                                                lean_inc_ref(v_curr_3213_);
                                                v___x_3296_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0(v_root_3214_, v_snd_3250_, v_curr_3213_, v___x_3257_, v___x_3295_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
                                                v___y_3228_ = v___x_3296_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_fst_3282_);
                                            lean_dec(v___x_3257_);
                                            lean_dec(v_snd_3250_);
                                            lean_dec_ref(v_curr_3213_);
                                            v_a_3297_ = lean_ctor_get(v___x_3290_, 0);
                                            v_isSharedCheck_3304_ =
                                                (!lean_is_exclusive(v___x_3290_)) as u8;
                                            if v_isSharedCheck_3304_ == 0 {
                                                v___x_3299_ = v___x_3290_;
                                                v_isShared_3300_ = v_isSharedCheck_3304_;
                                                state = 8;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3297_);
                                                lean_dec(v___x_3290_);
                                                v___x_3299_ = lean_box(0);
                                                v_isShared_3300_ = v_isSharedCheck_3304_;
                                                state = 8;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_fst_3282_);
                                    lean_dec(v___x_3257_);
                                    lean_dec(v_snd_3250_);
                                    lean_dec_ref(v_curr_3213_);
                                    v_a_3305_ = lean_ctor_get(v___x_3285_, 0);
                                    v_isSharedCheck_3312_ = (!lean_is_exclusive(v___x_3285_)) as u8;
                                    if v_isSharedCheck_3312_ == 0 {
                                        v___x_3307_ = v___x_3285_;
                                        v_isShared_3308_ = v_isSharedCheck_3312_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3305_);
                                        lean_dec(v___x_3285_);
                                        v___x_3307_ = lean_box(0);
                                        v_isShared_3308_ = v_isSharedCheck_3312_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_snd_3250_);
                    lean_dec(v_fst_3249_);
                    lean_dec_ref(v_curr_3213_);
                    v_a_3313_ = lean_ctor_get(v___x_3251_, 0);
                    v_isSharedCheck_3320_ = (!lean_is_exclusive(v___x_3251_)) as u8;
                    if v_isSharedCheck_3320_ == 0 {
                        v___x_3315_ = v___x_3251_;
                        v_isShared_3316_ = v_isSharedCheck_3320_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3313_);
                        lean_dec(v___x_3251_);
                        v___x_3315_ = lean_box(0);
                        v_isShared_3316_ = v_isSharedCheck_3320_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_3228_) == 0 {
                    v_a_3229_ = lean_ctor_get(v___y_3228_, 0);
                    v_isSharedCheck_3239_ = (!lean_is_exclusive(v___y_3228_)) as u8;
                    if v_isSharedCheck_3239_ == 0 {
                        v___x_3231_ = v___y_3228_;
                        v_isShared_3232_ = v_isSharedCheck_3239_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3229_);
                        lean_dec(v___y_3228_);
                        v___x_3231_ = lean_box(0);
                        v_isShared_3232_ = v_isSharedCheck_3239_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_curr_3213_);
                    v_a_3240_ = lean_ctor_get(v___y_3228_, 0);
                    v_isSharedCheck_3247_ = (!lean_is_exclusive(v___y_3228_)) as u8;
                    if v_isSharedCheck_3247_ == 0 {
                        v___x_3242_ = v___y_3228_;
                        v_isShared_3243_ = v_isSharedCheck_3247_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3240_);
                        lean_dec(v___y_3228_);
                        v___x_3242_ = lean_box(0);
                        v_isShared_3243_ = v_isSharedCheck_3247_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3229_) == 0 {
                    lean_dec_ref(v_curr_3213_);
                    v_a_3233_ = lean_ctor_get(v_a_3229_, 0);
                    lean_inc(v_a_3233_);
                    lean_dec_ref_known(v_a_3229_, 1);
                    if v_isShared_3232_ == 0 {
                        lean_ctor_set(v___x_3231_, 0, v_a_3233_);
                        v___x_3235_ = v___x_3231_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3233_);
                        v___x_3235_ = v_reuseFailAlloc_3236_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3231_);
                    v_a_3237_ = lean_ctor_get(v_a_3229_, 0);
                    lean_inc(v_a_3237_);
                    lean_dec_ref_known(v_a_3229_, 1);
                    v_a_3215_ = v_a_3237_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_3235_;
            }
            4 => {
                if v_isShared_3243_ == 0 {
                    v___x_3245_ = v___x_3242_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
                    v___x_3245_ = v_reuseFailAlloc_3246_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3245_;
            }
            6 => {
                if v_isShared_3276_ == 0 {
                    v___x_3278_ = v___x_3275_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
                    v___x_3278_ = v_reuseFailAlloc_3279_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3278_;
            }
            8 => {
                if v_isShared_3300_ == 0 {
                    v___x_3302_ = v___x_3299_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
                    v___x_3302_ = v_reuseFailAlloc_3303_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3302_;
            }
            10 => {
                if v_isShared_3308_ == 0 {
                    v___x_3310_ = v___x_3307_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
                    v___x_3310_ = v_reuseFailAlloc_3311_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3310_;
            }
            12 => {
                if v_isShared_3316_ == 0 {
                    v___x_3318_ = v___x_3315_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
                    v___x_3318_ = v_reuseFailAlloc_3319_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___boxed(
    mut v_curr_3321_: *mut LeanObject,
    mut v_root_3322_: *mut LeanObject,
    mut v_a_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
    mut v___y_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3335_: *mut LeanObject = core::ptr::null_mut();
    v_res_3335_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_3321_, v_root_3322_, v_a_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
    lean_dec(v___y_3333_);
    lean_dec_ref(v___y_3332_);
    lean_dec(v___y_3331_);
    lean_dec_ref(v___y_3330_);
    lean_dec(v___y_3329_);
    lean_dec_ref(v___y_3328_);
    lean_dec(v___y_3327_);
    lean_dec_ref(v___y_3326_);
    lean_dec(v___y_3325_);
    lean_dec(v___y_3324_);
    lean_dec_ref(v_root_3322_);
    return v_res_3335_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1()
-> *mut LeanObject {
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    v___x_3337_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__0;
    v___x_3338_ = lean_unsigned_to_nat(2);
    v___x_3339_ = lean_unsigned_to_nat(46);
    v___x_3340_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__1;
    v___x_3341_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_3342_ = l_mkPanicMessageWithDecl(
        v___x_3341_,
        v___x_3340_,
        v___x_3339_,
        v___x_3338_,
        v___x_3337_,
    );
    return v___x_3342_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(
    mut v_root_3343_: *mut LeanObject,
    mut v_a_3344_: *mut LeanObject,
    mut v_a_3345_: *mut LeanObject,
    mut v_a_3346_: *mut LeanObject,
    mut v_a_3347_: *mut LeanObject,
    mut v_a_3348_: *mut LeanObject,
    mut v_a_3349_: *mut LeanObject,
    mut v_a_3350_: *mut LeanObject,
    mut v_a_3351_: *mut LeanObject,
    mut v_a_3352_: *mut LeanObject,
    mut v_a_3353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_self_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3363_: u8 = 0;
    let mut v_fst_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3372_: u8 = 0;
    let mut v_a_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3376_: u8 = 0;
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_self_3355_ = lean_ctor_get(v_root_3343_, 0);
                lean_inc_ref_n(v_self_3355_, 2);
                v_size_3356_ = lean_ctor_get(v_root_3343_, 6);
                lean_inc(v_size_3356_);
                v_size_3357_ = lean_unsigned_to_nat(0);
                v___x_3358_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3358_, 0, v_size_3357_);
                lean_ctor_set(v___x_3358_, 1, v_self_3355_);
                v___x_3359_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_self_3355_, v_root_3343_, v___x_3358_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_);
                lean_dec_ref(v_root_3343_);
                if lean_obj_tag(v___x_3359_) == 0 {
                    v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
                    v_isSharedCheck_3372_ = (!lean_is_exclusive(v___x_3359_)) as u8;
                    if v_isSharedCheck_3372_ == 0 {
                        v___x_3362_ = v___x_3359_;
                        v_isShared_3363_ = v_isSharedCheck_3372_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3360_);
                        lean_dec(v___x_3359_);
                        v___x_3362_ = lean_box(0);
                        v_isShared_3363_ = v_isSharedCheck_3372_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_size_3356_);
                    v_a_3373_ = lean_ctor_get(v___x_3359_, 0);
                    v_isSharedCheck_3380_ = (!lean_is_exclusive(v___x_3359_)) as u8;
                    if v_isSharedCheck_3380_ == 0 {
                        v___x_3375_ = v___x_3359_;
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3373_);
                        lean_dec(v___x_3359_);
                        v___x_3375_ = lean_box(0);
                        v_isShared_3376_ = v_isSharedCheck_3380_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3364_ = lean_ctor_get(v_a_3360_, 0);
                lean_inc(v_fst_3364_);
                lean_dec(v_a_3360_);
                v___x_3365_ = lean_nat_dec_eq(v_size_3356_, v_fst_3364_);
                lean_dec(v_fst_3364_);
                lean_dec(v_size_3356_);
                if v___x_3365_ == 0 {
                    lean_del_object(v___x_3362_);
                    v___x_3366_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___closed__1);
                    v___x_3367_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_3366_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_);
                    return v___x_3367_;
                } else {
                    v___x_3368_ = lean_box(0);
                    if v_isShared_3363_ == 0 {
                        lean_ctor_set(v___x_3362_, 0, v___x_3368_);
                        v___x_3370_ = v___x_3362_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
                        v___x_3370_ = v_reuseFailAlloc_3371_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3370_;
            }
            3 => {
                if v_isShared_3376_ == 0 {
                    v___x_3378_ = v___x_3375_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
                    v___x_3378_ = v_reuseFailAlloc_3379_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc___boxed(
    mut v_root_3381_: *mut LeanObject,
    mut v_a_3382_: *mut LeanObject,
    mut v_a_3383_: *mut LeanObject,
    mut v_a_3384_: *mut LeanObject,
    mut v_a_3385_: *mut LeanObject,
    mut v_a_3386_: *mut LeanObject,
    mut v_a_3387_: *mut LeanObject,
    mut v_a_3388_: *mut LeanObject,
    mut v_a_3389_: *mut LeanObject,
    mut v_a_3390_: *mut LeanObject,
    mut v_a_3391_: *mut LeanObject,
    mut v_a_3392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3393_: *mut LeanObject = core::ptr::null_mut();
    v_res_3393_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(
        v_root_3381_,
        v_a_3382_,
        v_a_3383_,
        v_a_3384_,
        v_a_3385_,
        v_a_3386_,
        v_a_3387_,
        v_a_3388_,
        v_a_3389_,
        v_a_3390_,
        v_a_3391_,
    );
    lean_dec(v_a_3391_);
    lean_dec_ref(v_a_3390_);
    lean_dec(v_a_3389_);
    lean_dec_ref(v_a_3388_);
    lean_dec(v_a_3387_);
    lean_dec_ref(v_a_3386_);
    lean_dec(v_a_3385_);
    lean_dec_ref(v_a_3384_);
    lean_dec(v_a_3383_);
    lean_dec(v_a_3382_);
    return v_res_3393_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(
    mut v_inst_3394_: *mut LeanObject,
    mut v_a_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
    mut v___y_3400_: *mut LeanObject,
    mut v___y_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
    mut v___y_3403_: *mut LeanObject,
    mut v___y_3404_: *mut LeanObject,
    mut v___y_3405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    v___x_3407_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___redArg(v_a_3395_, v___y_3396_);
    return v___x_3407_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1___boxed(
    mut v_inst_3408_: *mut LeanObject,
    mut v_a_3409_: *mut LeanObject,
    mut v___y_3410_: *mut LeanObject,
    mut v___y_3411_: *mut LeanObject,
    mut v___y_3412_: *mut LeanObject,
    mut v___y_3413_: *mut LeanObject,
    mut v___y_3414_: *mut LeanObject,
    mut v___y_3415_: *mut LeanObject,
    mut v___y_3416_: *mut LeanObject,
    mut v___y_3417_: *mut LeanObject,
    mut v___y_3418_: *mut LeanObject,
    mut v___y_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3421_: *mut LeanObject = core::ptr::null_mut();
    v_res_3421_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__1(v_inst_3408_, v_a_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
    lean_dec(v___y_3419_);
    lean_dec_ref(v___y_3418_);
    lean_dec(v___y_3417_);
    lean_dec_ref(v___y_3416_);
    lean_dec(v___y_3415_);
    lean_dec_ref(v___y_3414_);
    lean_dec(v___y_3413_);
    lean_dec_ref(v___y_3412_);
    lean_dec(v___y_3411_);
    lean_dec(v___y_3410_);
    return v_res_3421_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(
    mut v___x_3422_: *mut LeanObject,
    mut v_00_u03b2_3423_: *mut LeanObject,
    mut v_x_3424_: *mut LeanObject,
    mut v_x_3425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    v___x_3426_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___redArg(v___x_3422_, v_x_3424_, v_x_3425_);
    return v___x_3426_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2___boxed(
    mut v___x_3427_: *mut LeanObject,
    mut v_00_u03b2_3428_: *mut LeanObject,
    mut v_x_3429_: *mut LeanObject,
    mut v_x_3430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3431_: *mut LeanObject = core::ptr::null_mut();
    v_res_3431_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2(v___x_3427_, v_00_u03b2_3428_, v_x_3429_, v_x_3430_);
    lean_dec_ref(v_x_3429_);
    lean_dec_ref(v___x_3427_);
    return v_res_3431_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(
    mut v_curr_3432_: *mut LeanObject,
    mut v_root_3433_: *mut LeanObject,
    mut v_inst_3434_: *mut LeanObject,
    mut v_a_3435_: *mut LeanObject,
    mut v___y_3436_: *mut LeanObject,
    mut v___y_3437_: *mut LeanObject,
    mut v___y_3438_: *mut LeanObject,
    mut v___y_3439_: *mut LeanObject,
    mut v___y_3440_: *mut LeanObject,
    mut v___y_3441_: *mut LeanObject,
    mut v___y_3442_: *mut LeanObject,
    mut v___y_3443_: *mut LeanObject,
    mut v___y_3444_: *mut LeanObject,
    mut v___y_3445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    v___x_3447_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg(v_curr_3432_, v_root_3433_, v_a_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
    return v___x_3447_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___boxed(
    mut v_curr_3448_: *mut LeanObject,
    mut v_root_3449_: *mut LeanObject,
    mut v_inst_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
    mut v___y_3452_: *mut LeanObject,
    mut v___y_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
    mut v___y_3455_: *mut LeanObject,
    mut v___y_3456_: *mut LeanObject,
    mut v___y_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
    mut v___y_3462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3463_: *mut LeanObject = core::ptr::null_mut();
    v_res_3463_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3(v_curr_3448_, v_root_3449_, v_inst_3450_, v_a_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
    lean_dec(v___y_3461_);
    lean_dec_ref(v___y_3460_);
    lean_dec(v___y_3459_);
    lean_dec_ref(v___y_3458_);
    lean_dec(v___y_3457_);
    lean_dec_ref(v___y_3456_);
    lean_dec(v___y_3455_);
    lean_dec_ref(v___y_3454_);
    lean_dec(v___y_3453_);
    lean_dec(v___y_3452_);
    lean_dec_ref(v_root_3449_);
    return v_res_3463_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(
    mut v___x_3464_: *mut LeanObject,
    mut v_00_u03b2_3465_: *mut LeanObject,
    mut v_x_3466_: *mut LeanObject,
    mut v_x_3467_: usize,
    mut v_x_3468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_x_3466_);
    v___x_3469_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___redArg(v___x_3464_, v_x_3466_, v_x_3467_, v_x_3468_);
    return v___x_3469_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2___boxed(
    mut v___x_3470_: *mut LeanObject,
    mut v_00_u03b2_3471_: *mut LeanObject,
    mut v_x_3472_: *mut LeanObject,
    mut v_x_3473_: *mut LeanObject,
    mut v_x_3474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_33719__boxed_3475_: usize = 0;
    let mut v_res_3476_: *mut LeanObject = core::ptr::null_mut();
    v_x_33719__boxed_3475_ = lean_unbox_usize(v_x_3473_);
    lean_dec(v_x_3473_);
    v_res_3476_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2(v___x_3470_, v_00_u03b2_3471_, v_x_3472_, v_x_33719__boxed_3475_, v_x_3474_);
    lean_dec_ref(v_x_3472_);
    lean_dec_ref(v___x_3470_);
    return v_res_3476_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(
    mut v___x_3477_: *mut LeanObject,
    mut v_00_u03b2_3478_: *mut LeanObject,
    mut v_keys_3479_: *mut LeanObject,
    mut v_vals_3480_: *mut LeanObject,
    mut v_heq_3481_: *mut LeanObject,
    mut v_i_3482_: *mut LeanObject,
    mut v_k_3483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    v___x_3484_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___redArg(v___x_3477_, v_keys_3479_, v_vals_3480_, v_i_3482_, v_k_3483_);
    return v___x_3484_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4___boxed(
    mut v___x_3485_: *mut LeanObject,
    mut v_00_u03b2_3486_: *mut LeanObject,
    mut v_keys_3487_: *mut LeanObject,
    mut v_vals_3488_: *mut LeanObject,
    mut v_heq_3489_: *mut LeanObject,
    mut v_i_3490_: *mut LeanObject,
    mut v_k_3491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3492_: *mut LeanObject = core::ptr::null_mut();
    v_res_3492_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__2_spec__2_spec__4(v___x_3485_, v_00_u03b2_3486_, v_keys_3487_, v_vals_3488_, v_heq_3489_, v_i_3490_, v_k_3491_);
    lean_dec_ref(v_vals_3488_);
    lean_dec_ref(v_keys_3487_);
    lean_dec_ref(v___x_3485_);
    return v_res_3492_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(
    mut v_e_3493_: *mut LeanObject,
    mut v_child_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3502_: u8 = 0;
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3508_: u8 = 0;
    let mut v___x_3509_: u8 = 0;
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3497_ = lean_st_ref_get(v_a_3495_);
                v___x_3498_ = l_Lean_Meta_Grind_Goal_getRoot_x3f(v___x_3497_, v_child_3494_);
                lean_dec(v___x_3497_);
                if lean_obj_tag(v___x_3498_) == 1 {
                    v_val_3499_ = lean_ctor_get(v___x_3498_, 0);
                    v_isSharedCheck_3508_ = (!lean_is_exclusive(v___x_3498_)) as u8;
                    if v_isSharedCheck_3508_ == 0 {
                        v___x_3501_ = v___x_3498_;
                        v_isShared_3502_ = v_isSharedCheck_3508_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3499_);
                        lean_dec(v___x_3498_);
                        v___x_3501_ = lean_box(0);
                        v_isShared_3502_ = v_isSharedCheck_3508_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3498_);
                    v___x_3509_ = 0;
                    v___x_3510_ = lean_box((v___x_3509_) as usize);
                    v___x_3511_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3511_, 0, v___x_3510_);
                    return v___x_3511_;
                }
            }
            1 => {
                v___x_3503_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_val_3499_,
                        v_e_3493_,
                    );
                lean_dec(v_val_3499_);
                v___x_3504_ = lean_box((v___x_3503_) as usize);
                if v_isShared_3502_ == 0 {
                    lean_ctor_set_tag(v___x_3501_, 0);
                    lean_ctor_set(v___x_3501_, 0, v___x_3504_);
                    v___x_3506_ = v___x_3501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
                    v___x_3506_ = v_reuseFailAlloc_3507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg___boxed(
    mut v_e_3512_: *mut LeanObject,
    mut v_child_3513_: *mut LeanObject,
    mut v_a_3514_: *mut LeanObject,
    mut v_a_3515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3516_: *mut LeanObject = core::ptr::null_mut();
    v_res_3516_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(
        v_e_3512_,
        v_child_3513_,
        v_a_3514_,
    );
    lean_dec(v_a_3514_);
    lean_dec_ref(v_child_3513_);
    lean_dec_ref(v_e_3512_);
    return v_res_3516_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(
    mut v_e_3517_: *mut LeanObject,
    mut v_child_3518_: *mut LeanObject,
    mut v_a_3519_: *mut LeanObject,
    mut v_a_3520_: *mut LeanObject,
    mut v_a_3521_: *mut LeanObject,
    mut v_a_3522_: *mut LeanObject,
    mut v_a_3523_: *mut LeanObject,
    mut v_a_3524_: *mut LeanObject,
    mut v_a_3525_: *mut LeanObject,
    mut v_a_3526_: *mut LeanObject,
    mut v_a_3527_: *mut LeanObject,
    mut v_a_3528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    v___x_3530_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(
        v_e_3517_,
        v_child_3518_,
        v_a_3519_,
    );
    return v___x_3530_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___boxed(
    mut v_e_3531_: *mut LeanObject,
    mut v_child_3532_: *mut LeanObject,
    mut v_a_3533_: *mut LeanObject,
    mut v_a_3534_: *mut LeanObject,
    mut v_a_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
    mut v_a_3537_: *mut LeanObject,
    mut v_a_3538_: *mut LeanObject,
    mut v_a_3539_: *mut LeanObject,
    mut v_a_3540_: *mut LeanObject,
    mut v_a_3541_: *mut LeanObject,
    mut v_a_3542_: *mut LeanObject,
    mut v_a_3543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3544_: *mut LeanObject = core::ptr::null_mut();
    v_res_3544_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild(
        v_e_3531_,
        v_child_3532_,
        v_a_3533_,
        v_a_3534_,
        v_a_3535_,
        v_a_3536_,
        v_a_3537_,
        v_a_3538_,
        v_a_3539_,
        v_a_3540_,
        v_a_3541_,
        v_a_3542_,
    );
    lean_dec(v_a_3542_);
    lean_dec_ref(v_a_3541_);
    lean_dec(v_a_3540_);
    lean_dec_ref(v_a_3539_);
    lean_dec(v_a_3538_);
    lean_dec_ref(v_a_3537_);
    lean_dec(v_a_3536_);
    lean_dec_ref(v_a_3535_);
    lean_dec(v_a_3534_);
    lean_dec(v_a_3533_);
    lean_dec_ref(v_child_3532_);
    lean_dec_ref(v_e_3531_);
    return v_res_3544_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(
    mut v___x_3545_: *mut LeanObject,
    mut v_body_3546_: *mut LeanObject,
    mut v_____r_3547_: *mut LeanObject,
    mut v___y_3548_: *mut LeanObject,
    mut v___y_3549_: *mut LeanObject,
    mut v___y_3550_: *mut LeanObject,
    mut v___y_3551_: *mut LeanObject,
    mut v___y_3552_: *mut LeanObject,
    mut v___y_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
    mut v___y_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    v___x_3559_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3559_, 0, v___x_3545_);
    lean_ctor_set(v___x_3559_, 1, v_body_3546_);
    v___x_3560_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3560_, 0, v___x_3559_);
    v___x_3561_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3561_, 0, v___x_3560_);
    return v___x_3561_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed(
    mut v___x_3562_: *mut LeanObject,
    mut v_body_3563_: *mut LeanObject,
    mut v_____r_3564_: *mut LeanObject,
    mut v___y_3565_: *mut LeanObject,
    mut v___y_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
    mut v___y_3570_: *mut LeanObject,
    mut v___y_3571_: *mut LeanObject,
    mut v___y_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
    mut v___y_3574_: *mut LeanObject,
    mut v___y_3575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3576_: *mut LeanObject = core::ptr::null_mut();
    v_res_3576_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_3562_, v_body_3563_, v_____r_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
    lean_dec(v___y_3574_);
    lean_dec_ref(v___y_3573_);
    lean_dec(v___y_3572_);
    lean_dec_ref(v___y_3571_);
    lean_dec(v___y_3570_);
    lean_dec_ref(v___y_3569_);
    lean_dec(v___y_3568_);
    lean_dec_ref(v___y_3567_);
    lean_dec(v___y_3566_);
    lean_dec(v___y_3565_);
    return v_res_3576_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(
    mut v___f_3577_: *mut LeanObject,
    mut v_x_3578_: *mut LeanObject,
    mut v___y_3579_: *mut LeanObject,
    mut v___y_3580_: *mut LeanObject,
    mut v___y_3581_: *mut LeanObject,
    mut v___y_3582_: *mut LeanObject,
    mut v___y_3583_: *mut LeanObject,
    mut v___y_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
    mut v___y_3586_: *mut LeanObject,
    mut v___y_3587_: *mut LeanObject,
    mut v___y_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    v___x_3590_ = lean_box(0);
    lean_inc(v___y_3588_);
    lean_inc_ref(v___y_3587_);
    lean_inc(v___y_3586_);
    lean_inc_ref(v___y_3585_);
    lean_inc(v___y_3584_);
    lean_inc_ref(v___y_3583_);
    lean_inc(v___y_3582_);
    lean_inc_ref(v___y_3581_);
    lean_inc(v___y_3580_);
    lean_inc(v___y_3579_);
    v___x_3591_ = lean_apply_12(
        v___f_3577_,
        v___x_3590_,
        v___y_3579_,
        v___y_3580_,
        v___y_3581_,
        v___y_3582_,
        v___y_3583_,
        v___y_3584_,
        v___y_3585_,
        v___y_3586_,
        v___y_3587_,
        v___y_3588_,
        lean_box(0),
    );
    return v___x_3591_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1___boxed(
    mut v___f_3592_: *mut LeanObject,
    mut v_x_3593_: *mut LeanObject,
    mut v___y_3594_: *mut LeanObject,
    mut v___y_3595_: *mut LeanObject,
    mut v___y_3596_: *mut LeanObject,
    mut v___y_3597_: *mut LeanObject,
    mut v___y_3598_: *mut LeanObject,
    mut v___y_3599_: *mut LeanObject,
    mut v___y_3600_: *mut LeanObject,
    mut v___y_3601_: *mut LeanObject,
    mut v___y_3602_: *mut LeanObject,
    mut v___y_3603_: *mut LeanObject,
    mut v___y_3604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3605_: *mut LeanObject = core::ptr::null_mut();
    v_res_3605_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_3592_, v_x_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_);
    lean_dec(v___y_3603_);
    lean_dec_ref(v___y_3602_);
    lean_dec(v___y_3601_);
    lean_dec_ref(v___y_3600_);
    lean_dec(v___y_3599_);
    lean_dec_ref(v___y_3598_);
    lean_dec(v___y_3597_);
    lean_dec_ref(v___y_3596_);
    lean_dec(v___y_3595_);
    lean_dec(v___y_3594_);
    return v_res_3605_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(
    mut v_e_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
    mut v___y_3617_: *mut LeanObject,
    mut v___y_3618_: *mut LeanObject,
    mut v___y_3619_: *mut LeanObject,
    mut v___y_3620_: *mut LeanObject,
    mut v___y_3621_: *mut LeanObject,
    mut v___y_3622_: *mut LeanObject,
    mut v___y_3623_: *mut LeanObject,
    mut v___y_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3633_: u8 = 0;
    let mut v_a_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut v_a_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v_snd_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3652_: u8 = 0;
    let mut v_binderType_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: u8 = 0;
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: u8 = 0;
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: u8 = 0;
    let mut v___x_3676_: u8 = 0;
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: u8 = 0;
    let mut v___y_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3688_: u8 = 0;
    let mut v___x_3689_: u8 = 0;
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3700_: u8 = 0;
    let mut v_a_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3708_: u8 = 0;
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: u8 = 0;
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3719_: u8 = 0;
    let mut v___x_3720_: u8 = 0;
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3731_: u8 = 0;
    let mut v_a_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3735_: u8 = 0;
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3739_: u8 = 0;
    let mut v_a_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3743_: u8 = 0;
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3747_: u8 = 0;
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3753_: u8 = 0;
    let mut v_unused_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3649_ = lean_ctor_get(v_a_3616_, 1);
                v_isSharedCheck_3753_ = (!lean_is_exclusive(v_a_3616_)) as u8;
                if v_isSharedCheck_3753_ == 0 {
                    v_unused_3754_ = lean_ctor_get(v_a_3616_, 0);
                    lean_dec(v_unused_3754_);
                    v___x_3651_ = v_a_3616_;
                    v_isShared_3652_ = v_isSharedCheck_3753_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_snd_3649_);
                    lean_dec(v_a_3616_);
                    v___x_3651_ = lean_box(0);
                    v_isShared_3652_ = v_isSharedCheck_3753_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v___y_3629_) == 0 {
                    v_a_3630_ = lean_ctor_get(v___y_3629_, 0);
                    v_isSharedCheck_3640_ = (!lean_is_exclusive(v___y_3629_)) as u8;
                    if v_isSharedCheck_3640_ == 0 {
                        v___x_3632_ = v___y_3629_;
                        v_isShared_3633_ = v_isSharedCheck_3640_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3630_);
                        lean_dec(v___y_3629_);
                        v___x_3632_ = lean_box(0);
                        v_isShared_3633_ = v_isSharedCheck_3640_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3641_ = lean_ctor_get(v___y_3629_, 0);
                    v_isSharedCheck_3648_ = (!lean_is_exclusive(v___y_3629_)) as u8;
                    if v_isSharedCheck_3648_ == 0 {
                        v___x_3643_ = v___y_3629_;
                        v_isShared_3644_ = v_isSharedCheck_3648_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3641_);
                        lean_dec(v___y_3629_);
                        v___x_3643_ = lean_box(0);
                        v_isShared_3644_ = v_isSharedCheck_3648_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3630_) == 0 {
                    v_a_3634_ = lean_ctor_get(v_a_3630_, 0);
                    lean_inc(v_a_3634_);
                    lean_dec_ref_known(v_a_3630_, 1);
                    if v_isShared_3633_ == 0 {
                        lean_ctor_set(v___x_3632_, 0, v_a_3634_);
                        v___x_3636_ = v___x_3632_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3634_);
                        v___x_3636_ = v_reuseFailAlloc_3637_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3632_);
                    v_a_3638_ = lean_ctor_get(v_a_3630_, 0);
                    lean_inc(v_a_3638_);
                    lean_dec_ref_known(v_a_3630_, 1);
                    v_a_3616_ = v_a_3638_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_3636_;
            }
            4 => {
                if v_isShared_3644_ == 0 {
                    v___x_3646_ = v___x_3643_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
                    v___x_3646_ = v_reuseFailAlloc_3647_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3646_;
            }
            6 => {
                if lean_obj_tag(v_snd_3649_) == 7 {
                    v_binderType_3653_ = lean_ctor_get(v_snd_3649_, 1);
                    v_body_3654_ = lean_ctor_get(v_snd_3649_, 2);
                    lean_inc_ref(v_binderType_3653_);
                    v___x_3655_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                        v_binderType_3653_,
                        v___y_3624_,
                    );
                    if lean_obj_tag(v___x_3655_) == 0 {
                        v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
                        lean_inc(v_a_3656_);
                        lean_dec_ref_known(v___x_3655_, 1);
                        v___x_3657_ = lean_box(0);
                        lean_inc_ref(v_body_3654_);
                        v___f_3658_ = lean_alloc_closure(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 2);
                        lean_closure_set(v___f_3658_, 0, v___x_3657_);
                        lean_closure_set(v___f_3658_, 1, v_body_3654_);
                        v___x_3659_ = l_Lean_Expr_cleanupAnnotations(v_a_3656_);
                        v___x_3660_ = l_Lean_Expr_isApp(v___x_3659_);
                        if v___x_3660_ == 0 {
                            lean_dec_ref(v___x_3659_);
                            lean_dec_ref_known(v_snd_3649_, 3);
                            lean_del_object(v___x_3651_);
                            v___x_3661_ = lean_box(0);
                            v___x_3662_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_3658_, v___x_3661_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
                            v___y_3629_ = v___x_3662_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3663_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3659_);
                            v___x_3664_ = l_Lean_Expr_isApp(v___x_3663_);
                            if v___x_3664_ == 0 {
                                lean_dec_ref(v___x_3663_);
                                lean_dec_ref_known(v_snd_3649_, 3);
                                lean_del_object(v___x_3651_);
                                v___x_3665_ = lean_box(0);
                                v___x_3666_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_3658_, v___x_3665_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
                                v___y_3629_ = v___x_3666_;
                                state = 1;
                                continue;
                            } else {
                                v_arg_3667_ = lean_ctor_get(v___x_3663_, 1);
                                lean_inc_ref(v_arg_3667_);
                                v___x_3668_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3663_);
                                v___x_3669_ = l_Lean_Expr_isApp(v___x_3668_);
                                if v___x_3669_ == 0 {
                                    lean_dec_ref(v___x_3668_);
                                    lean_dec_ref(v_arg_3667_);
                                    lean_dec_ref_known(v_snd_3649_, 3);
                                    lean_del_object(v___x_3651_);
                                    v___x_3670_ = lean_box(0);
                                    v___x_3671_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_3658_, v___x_3670_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
                                    v___y_3629_ = v___x_3671_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_3672_ = lean_ctor_get(v___x_3668_, 1);
                                    lean_inc_ref(v_arg_3672_);
                                    v___x_3673_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3668_);
                                    v___x_3674_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__1;
                                    v___x_3675_ = l_Lean_Expr_isConstOf(v___x_3673_, v___x_3674_);
                                    if v___x_3675_ == 0 {
                                        lean_dec_ref(v_arg_3667_);
                                        v___x_3676_ = l_Lean_Expr_isApp(v___x_3673_);
                                        if v___x_3676_ == 0 {
                                            lean_dec_ref(v___x_3673_);
                                            lean_dec_ref(v_arg_3672_);
                                            lean_dec_ref_known(v_snd_3649_, 3);
                                            lean_del_object(v___x_3651_);
                                            v___x_3677_ = lean_box(0);
                                            v___x_3678_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_3658_, v___x_3677_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
                                            v___y_3629_ = v___x_3678_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v_arg_3679_ = lean_ctor_get(v___x_3673_, 1);
                                            lean_inc_ref(v_arg_3679_);
                                            v___x_3680_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3673_);
                                            v___x_3681_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__3;
                                            v___x_3682_ =
                                                l_Lean_Expr_isConstOf(v___x_3680_, v___x_3681_);
                                            lean_dec_ref(v___x_3680_);
                                            if v___x_3682_ == 0 {
                                                lean_dec_ref(v_arg_3679_);
                                                lean_dec_ref(v_arg_3672_);
                                                lean_dec_ref_known(v_snd_3649_, 3);
                                                lean_del_object(v___x_3651_);
                                                v___x_3709_ = lean_box(0);
                                                v___x_3710_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__1(v___f_3658_, v___x_3709_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
                                                v___y_3629_ = v___x_3710_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___f_3658_);
                                                v___x_3711_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_3615_, v_arg_3679_, v___y_3617_);
                                                lean_dec_ref(v_arg_3679_);
                                                if lean_obj_tag(v___x_3711_) == 0 {
                                                    v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
                                                    lean_inc(v_a_3712_);
                                                    v___x_3713_ = (lean_unbox(v_a_3712_) as u8);
                                                    lean_dec(v_a_3712_);
                                                    if v___x_3713_ == 0 {
                                                        lean_dec_ref_known(v___x_3711_, 1);
                                                        v___x_3714_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_3615_, v_arg_3672_, v___y_3617_);
                                                        lean_dec_ref(v_arg_3672_);
                                                        v___y_3684_ = v___x_3714_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        lean_dec_ref(v_arg_3672_);
                                                        v___y_3684_ = v___x_3711_;
                                                        state = 7;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_arg_3672_);
                                                    v___y_3684_ = v___x_3711_;
                                                    state = 7;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_3673_);
                                        lean_dec_ref(v_arg_3672_);
                                        lean_dec_ref(v___f_3658_);
                                        v___x_3715_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_3615_, v_arg_3667_, v___y_3617_);
                                        lean_dec_ref(v_arg_3667_);
                                        if lean_obj_tag(v___x_3715_) == 0 {
                                            v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
                                            v_isSharedCheck_3731_ =
                                                (!lean_is_exclusive(v___x_3715_)) as u8;
                                            if v_isSharedCheck_3731_ == 0 {
                                                v___x_3718_ = v___x_3715_;
                                                v_isShared_3719_ = v_isSharedCheck_3731_;
                                                state = 13;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3716_);
                                                lean_dec(v___x_3715_);
                                                v___x_3718_ = lean_box(0);
                                                v_isShared_3719_ = v_isSharedCheck_3731_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref_known(v_snd_3649_, 3);
                                            lean_del_object(v___x_3651_);
                                            v_a_3732_ = lean_ctor_get(v___x_3715_, 0);
                                            v_isSharedCheck_3739_ =
                                                (!lean_is_exclusive(v___x_3715_)) as u8;
                                            if v_isSharedCheck_3739_ == 0 {
                                                v___x_3734_ = v___x_3715_;
                                                v_isShared_3735_ = v_isSharedCheck_3739_;
                                                state = 16;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3732_);
                                                lean_dec(v___x_3715_);
                                                v___x_3734_ = lean_box(0);
                                                v_isShared_3735_ = v_isSharedCheck_3739_;
                                                state = 16;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_snd_3649_, 3);
                        lean_del_object(v___x_3651_);
                        v_a_3740_ = lean_ctor_get(v___x_3655_, 0);
                        v_isSharedCheck_3747_ = (!lean_is_exclusive(v___x_3655_)) as u8;
                        if v_isSharedCheck_3747_ == 0 {
                            v___x_3742_ = v___x_3655_;
                            v_isShared_3743_ = v_isSharedCheck_3747_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_3740_);
                            lean_dec(v___x_3655_);
                            v___x_3742_ = lean_box(0);
                            v_isShared_3743_ = v_isSharedCheck_3747_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    v___x_3748_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___closed__4;
                    if v_isShared_3652_ == 0 {
                        lean_ctor_set(v___x_3651_, 0, v___x_3748_);
                        v___x_3750_ = v___x_3651_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3748_);
                        lean_ctor_set(v_reuseFailAlloc_3752_, 1, v_snd_3649_);
                        v___x_3750_ = v_reuseFailAlloc_3752_;
                        state = 20;
                        continue;
                    }
                }
            }
            7 => {
                if lean_obj_tag(v___y_3684_) == 0 {
                    v_a_3685_ = lean_ctor_get(v___y_3684_, 0);
                    v_isSharedCheck_3700_ = (!lean_is_exclusive(v___y_3684_)) as u8;
                    if v_isSharedCheck_3700_ == 0 {
                        v___x_3687_ = v___y_3684_;
                        v_isShared_3688_ = v_isSharedCheck_3700_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3685_);
                        lean_dec(v___y_3684_);
                        v___x_3687_ = lean_box(0);
                        v_isShared_3688_ = v_isSharedCheck_3700_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_snd_3649_, 3);
                    lean_del_object(v___x_3651_);
                    v_a_3701_ = lean_ctor_get(v___y_3684_, 0);
                    v_isSharedCheck_3708_ = (!lean_is_exclusive(v___y_3684_)) as u8;
                    if v_isSharedCheck_3708_ == 0 {
                        v___x_3703_ = v___y_3684_;
                        v_isShared_3704_ = v_isSharedCheck_3708_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3701_);
                        lean_dec(v___y_3684_);
                        v___x_3703_ = lean_box(0);
                        v_isShared_3704_ = v_isSharedCheck_3708_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3689_ = (lean_unbox(v_a_3685_) as u8);
                lean_dec(v_a_3685_);
                if v___x_3689_ == 0 {
                    lean_inc_ref(v_body_3654_);
                    lean_del_object(v___x_3687_);
                    lean_dec_ref_known(v_snd_3649_, 3);
                    lean_del_object(v___x_3651_);
                    v___x_3690_ = lean_box(0);
                    v___x_3691_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_3657_, v_body_3654_, v___x_3690_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
                    v___y_3629_ = v___x_3691_;
                    state = 1;
                    continue;
                } else {
                    v___x_3692_ = lean_box((v___x_3682_) as usize);
                    v___x_3693_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3693_, 0, v___x_3692_);
                    if v_isShared_3652_ == 0 {
                        lean_ctor_set(v___x_3651_, 0, v___x_3693_);
                        v___x_3695_ = v___x_3651_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3693_);
                        lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_snd_3649_);
                        v___x_3695_ = v_reuseFailAlloc_3699_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3688_ == 0 {
                    lean_ctor_set(v___x_3687_, 0, v___x_3695_);
                    v___x_3697_ = v___x_3687_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
                    v___x_3697_ = v_reuseFailAlloc_3698_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3697_;
            }
            11 => {
                if v_isShared_3704_ == 0 {
                    v___x_3706_ = v___x_3703_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
                    v___x_3706_ = v_reuseFailAlloc_3707_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3706_;
            }
            13 => {
                v___x_3720_ = (lean_unbox(v_a_3716_) as u8);
                lean_dec(v_a_3716_);
                if v___x_3720_ == 0 {
                    lean_inc_ref(v_body_3654_);
                    lean_del_object(v___x_3718_);
                    lean_dec_ref_known(v_snd_3649_, 3);
                    lean_del_object(v___x_3651_);
                    v___x_3721_ = lean_box(0);
                    v___x_3722_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___lam__0(v___x_3657_, v_body_3654_, v___x_3721_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
                    v___y_3629_ = v___x_3722_;
                    state = 1;
                    continue;
                } else {
                    v___x_3723_ = lean_box((v___x_3675_) as usize);
                    v___x_3724_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3724_, 0, v___x_3723_);
                    if v_isShared_3652_ == 0 {
                        lean_ctor_set(v___x_3651_, 0, v___x_3724_);
                        v___x_3726_ = v___x_3651_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3724_);
                        lean_ctor_set(v_reuseFailAlloc_3730_, 1, v_snd_3649_);
                        v___x_3726_ = v_reuseFailAlloc_3730_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_3719_ == 0 {
                    lean_ctor_set(v___x_3718_, 0, v___x_3726_);
                    v___x_3728_ = v___x_3718_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3726_);
                    v___x_3728_ = v_reuseFailAlloc_3729_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3728_;
            }
            16 => {
                if v_isShared_3735_ == 0 {
                    v___x_3737_ = v___x_3734_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
                    v___x_3737_ = v_reuseFailAlloc_3738_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3737_;
            }
            18 => {
                if v_isShared_3743_ == 0 {
                    v___x_3745_ = v___x_3742_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
                    v___x_3745_ = v_reuseFailAlloc_3746_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3745_;
            }
            20 => {
                v___x_3751_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3751_, 0, v___x_3750_);
                return v___x_3751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg___boxed(
    mut v_e_3755_: *mut LeanObject,
    mut v_a_3756_: *mut LeanObject,
    mut v___y_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
    mut v___y_3759_: *mut LeanObject,
    mut v___y_3760_: *mut LeanObject,
    mut v___y_3761_: *mut LeanObject,
    mut v___y_3762_: *mut LeanObject,
    mut v___y_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
    mut v___y_3766_: *mut LeanObject,
    mut v___y_3767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3768_: *mut LeanObject = core::ptr::null_mut();
    v_res_3768_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_3755_, v_a_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
    lean_dec(v___y_3766_);
    lean_dec_ref(v___y_3765_);
    lean_dec(v___y_3764_);
    lean_dec_ref(v___y_3763_);
    lean_dec(v___y_3762_);
    lean_dec_ref(v___y_3761_);
    lean_dec(v___y_3760_);
    lean_dec_ref(v___y_3759_);
    lean_dec(v___y_3758_);
    lean_dec(v___y_3757_);
    lean_dec_ref(v_e_3755_);
    return v_res_3768_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(
    mut v_e_3776_: *mut LeanObject,
    mut v_parent_3777_: *mut LeanObject,
    mut v_a_3778_: *mut LeanObject,
    mut v_a_3779_: *mut LeanObject,
    mut v_a_3780_: *mut LeanObject,
    mut v_a_3781_: *mut LeanObject,
    mut v_a_3782_: *mut LeanObject,
    mut v_a_3783_: *mut LeanObject,
    mut v_a_3784_: *mut LeanObject,
    mut v_a_3785_: *mut LeanObject,
    mut v_a_3786_: *mut LeanObject,
    mut v_a_3787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3793_: u8 = 0;
    let mut v___x_3795_: u8 = 0;
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: u8 = 0;
    let mut v_arg_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: u8 = 0;
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v_fst_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: u8 = 0;
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3823_: u8 = 0;
    let mut v_a_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3831_: u8 = 0;
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut v_a_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3789_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_parent_3777_, v_a_3785_);
                if lean_obj_tag(v___x_3789_) == 0 {
                    v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
                    v_isSharedCheck_3832_ = (!lean_is_exclusive(v___x_3789_)) as u8;
                    if v_isSharedCheck_3832_ == 0 {
                        v___x_3792_ = v___x_3789_;
                        v_isShared_3793_ = v_isSharedCheck_3832_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3790_);
                        lean_dec(v___x_3789_);
                        v___x_3792_ = lean_box(0);
                        v_isShared_3793_ = v_isSharedCheck_3832_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3833_ = lean_ctor_get(v___x_3789_, 0);
                    v_isSharedCheck_3840_ = (!lean_is_exclusive(v___x_3789_)) as u8;
                    if v_isSharedCheck_3840_ == 0 {
                        v___x_3835_ = v___x_3789_;
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3833_);
                        lean_dec(v___x_3789_);
                        v___x_3835_ = lean_box(0);
                        v_isShared_3836_ = v_isSharedCheck_3840_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3800_ = l_Lean_Expr_cleanupAnnotations(v_a_3790_);
                v___x_3801_ = l_Lean_Expr_isApp(v___x_3800_);
                if v___x_3801_ == 0 {
                    lean_dec_ref(v___x_3800_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3802_ = lean_ctor_get(v___x_3800_, 1);
                    lean_inc_ref(v_arg_3802_);
                    v___x_3803_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3800_);
                    v___x_3804_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___closed__3;
                    v___x_3805_ = l_Lean_Expr_isConstOf(v___x_3803_, v___x_3804_);
                    lean_dec_ref(v___x_3803_);
                    if v___x_3805_ == 0 {
                        lean_dec_ref(v_arg_3802_);
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_3792_);
                        v___x_3806_ = lean_box(0);
                        v___x_3807_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3807_, 0, v___x_3806_);
                        lean_ctor_set(v___x_3807_, 1, v_arg_3802_);
                        v___x_3808_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_3776_, v___x_3807_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
                        if lean_obj_tag(v___x_3808_) == 0 {
                            v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
                            v_isSharedCheck_3823_ = (!lean_is_exclusive(v___x_3808_)) as u8;
                            if v_isSharedCheck_3823_ == 0 {
                                v___x_3811_ = v___x_3808_;
                                v_isShared_3812_ = v_isSharedCheck_3823_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3809_);
                                lean_dec(v___x_3808_);
                                v___x_3811_ = lean_box(0);
                                v_isShared_3812_ = v_isSharedCheck_3823_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_3824_ = lean_ctor_get(v___x_3808_, 0);
                            v_isSharedCheck_3831_ = (!lean_is_exclusive(v___x_3808_)) as u8;
                            if v_isSharedCheck_3831_ == 0 {
                                v___x_3826_ = v___x_3808_;
                                v_isShared_3827_ = v_isSharedCheck_3831_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_3824_);
                                lean_dec(v___x_3808_);
                                v___x_3826_ = lean_box(0);
                                v_isShared_3827_ = v_isSharedCheck_3831_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3795_ = 0;
                v___x_3796_ = lean_box((v___x_3795_) as usize);
                if v_isShared_3793_ == 0 {
                    lean_ctor_set(v___x_3792_, 0, v___x_3796_);
                    v___x_3798_ = v___x_3792_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
                    v___x_3798_ = v_reuseFailAlloc_3799_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3798_;
            }
            4 => {
                v_fst_3813_ = lean_ctor_get(v_a_3809_, 0);
                lean_inc(v_fst_3813_);
                lean_dec(v_a_3809_);
                if lean_obj_tag(v_fst_3813_) == 0 {
                    v___x_3814_ = 0;
                    v___x_3815_ = lean_box((v___x_3814_) as usize);
                    if v_isShared_3812_ == 0 {
                        lean_ctor_set(v___x_3811_, 0, v___x_3815_);
                        v___x_3817_ = v___x_3811_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
                        v___x_3817_ = v_reuseFailAlloc_3818_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_3819_ = lean_ctor_get(v_fst_3813_, 0);
                    lean_inc(v_val_3819_);
                    lean_dec_ref_known(v_fst_3813_, 1);
                    if v_isShared_3812_ == 0 {
                        lean_ctor_set(v___x_3811_, 0, v_val_3819_);
                        v___x_3821_ = v___x_3811_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_val_3819_);
                        v___x_3821_ = v_reuseFailAlloc_3822_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3817_;
            }
            6 => {
                return v___x_3821_;
            }
            7 => {
                if v_isShared_3827_ == 0 {
                    v___x_3829_ = v___x_3826_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
                    v___x_3829_ = v_reuseFailAlloc_3830_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3829_;
            }
            9 => {
                if v_isShared_3836_ == 0 {
                    v___x_3838_ = v___x_3835_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
                    v___x_3838_ = v_reuseFailAlloc_3839_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent___boxed(
    mut v_e_3841_: *mut LeanObject,
    mut v_parent_3842_: *mut LeanObject,
    mut v_a_3843_: *mut LeanObject,
    mut v_a_3844_: *mut LeanObject,
    mut v_a_3845_: *mut LeanObject,
    mut v_a_3846_: *mut LeanObject,
    mut v_a_3847_: *mut LeanObject,
    mut v_a_3848_: *mut LeanObject,
    mut v_a_3849_: *mut LeanObject,
    mut v_a_3850_: *mut LeanObject,
    mut v_a_3851_: *mut LeanObject,
    mut v_a_3852_: *mut LeanObject,
    mut v_a_3853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3854_: *mut LeanObject = core::ptr::null_mut();
    v_res_3854_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(
        v_e_3841_,
        v_parent_3842_,
        v_a_3843_,
        v_a_3844_,
        v_a_3845_,
        v_a_3846_,
        v_a_3847_,
        v_a_3848_,
        v_a_3849_,
        v_a_3850_,
        v_a_3851_,
        v_a_3852_,
    );
    lean_dec(v_a_3852_);
    lean_dec_ref(v_a_3851_);
    lean_dec(v_a_3850_);
    lean_dec_ref(v_a_3849_);
    lean_dec(v_a_3848_);
    lean_dec_ref(v_a_3847_);
    lean_dec(v_a_3846_);
    lean_dec_ref(v_a_3845_);
    lean_dec(v_a_3844_);
    lean_dec(v_a_3843_);
    lean_dec_ref(v_e_3841_);
    return v_res_3854_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(
    mut v_e_3855_: *mut LeanObject,
    mut v_inst_3856_: *mut LeanObject,
    mut v_a_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
    mut v___y_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
    mut v___y_3861_: *mut LeanObject,
    mut v___y_3862_: *mut LeanObject,
    mut v___y_3863_: *mut LeanObject,
    mut v___y_3864_: *mut LeanObject,
    mut v___y_3865_: *mut LeanObject,
    mut v___y_3866_: *mut LeanObject,
    mut v___y_3867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    v___x_3869_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___redArg(v_e_3855_, v_a_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
    return v___x_3869_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0___boxed(
    mut v_e_3870_: *mut LeanObject,
    mut v_inst_3871_: *mut LeanObject,
    mut v_a_3872_: *mut LeanObject,
    mut v___y_3873_: *mut LeanObject,
    mut v___y_3874_: *mut LeanObject,
    mut v___y_3875_: *mut LeanObject,
    mut v___y_3876_: *mut LeanObject,
    mut v___y_3877_: *mut LeanObject,
    mut v___y_3878_: *mut LeanObject,
    mut v___y_3879_: *mut LeanObject,
    mut v___y_3880_: *mut LeanObject,
    mut v___y_3881_: *mut LeanObject,
    mut v___y_3882_: *mut LeanObject,
    mut v___y_3883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3884_: *mut LeanObject = core::ptr::null_mut();
    v_res_3884_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent_spec__0(v_e_3870_, v_inst_3871_, v_a_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
    lean_dec(v___y_3882_);
    lean_dec_ref(v___y_3881_);
    lean_dec(v___y_3880_);
    lean_dec_ref(v___y_3879_);
    lean_dec(v___y_3878_);
    lean_dec_ref(v___y_3877_);
    lean_dec(v___y_3876_);
    lean_dec_ref(v___y_3875_);
    lean_dec(v___y_3874_);
    lean_dec(v___y_3873_);
    lean_dec_ref(v_e_3870_);
    return v_res_3884_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    v___x_3885_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_3885_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(
    mut v_msg_3886_: *mut LeanObject,
    mut v___y_3887_: *mut LeanObject,
    mut v___y_3888_: *mut LeanObject,
    mut v___y_3889_: *mut LeanObject,
    mut v___y_3890_: *mut LeanObject,
    mut v___y_3891_: *mut LeanObject,
    mut v___y_3892_: *mut LeanObject,
    mut v___y_3893_: *mut LeanObject,
    mut v___y_3894_: *mut LeanObject,
    mut v___y_3895_: *mut LeanObject,
    mut v___y_3896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_59987__overap_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    v___x_3898_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___closed__0);
    v___x_59987__overap_3899_ = lean_panic_fn_borrowed(v___x_3898_, v_msg_3886_);
    lean_inc(v___y_3896_);
    lean_inc_ref(v___y_3895_);
    lean_inc(v___y_3894_);
    lean_inc_ref(v___y_3893_);
    lean_inc(v___y_3892_);
    lean_inc_ref(v___y_3891_);
    lean_inc(v___y_3890_);
    lean_inc_ref(v___y_3889_);
    lean_inc(v___y_3888_);
    lean_inc(v___y_3887_);
    v___x_3900_ = lean_apply_11(
        v___x_59987__overap_3899_,
        v___y_3887_,
        v___y_3888_,
        v___y_3889_,
        v___y_3890_,
        v___y_3891_,
        v___y_3892_,
        v___y_3893_,
        v___y_3894_,
        v___y_3895_,
        v___y_3896_,
        lean_box(0),
    );
    return v___x_3900_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0___boxed(
    mut v_msg_3901_: *mut LeanObject,
    mut v___y_3902_: *mut LeanObject,
    mut v___y_3903_: *mut LeanObject,
    mut v___y_3904_: *mut LeanObject,
    mut v___y_3905_: *mut LeanObject,
    mut v___y_3906_: *mut LeanObject,
    mut v___y_3907_: *mut LeanObject,
    mut v___y_3908_: *mut LeanObject,
    mut v___y_3909_: *mut LeanObject,
    mut v___y_3910_: *mut LeanObject,
    mut v___y_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3913_: *mut LeanObject = core::ptr::null_mut();
    v_res_3913_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v_msg_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
    lean_dec(v___y_3911_);
    lean_dec_ref(v___y_3910_);
    lean_dec(v___y_3909_);
    lean_dec_ref(v___y_3908_);
    lean_dec(v___y_3907_);
    lean_dec_ref(v___y_3906_);
    lean_dec(v___y_3905_);
    lean_dec_ref(v___y_3904_);
    lean_dec(v___y_3903_);
    lean_dec(v___y_3902_);
    return v_res_3913_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(
    mut v_msgData_3914_: *mut LeanObject,
    mut v___y_3915_: *mut LeanObject,
    mut v___y_3916_: *mut LeanObject,
    mut v___y_3917_: *mut LeanObject,
    mut v___y_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    v___x_3920_ = lean_st_ref_get(v___y_3918_);
    v_env_3921_ = lean_ctor_get(v___x_3920_, 0);
    lean_inc_ref(v_env_3921_);
    lean_dec(v___x_3920_);
    v___x_3922_ = lean_st_ref_get(v___y_3916_);
    v_mctx_3923_ = lean_ctor_get(v___x_3922_, 0);
    lean_inc_ref(v_mctx_3923_);
    lean_dec(v___x_3922_);
    v_lctx_3924_ = lean_ctor_get(v___y_3915_, 2);
    v_options_3925_ = lean_ctor_get(v___y_3917_, 2);
    lean_inc_ref(v_options_3925_);
    lean_inc_ref(v_lctx_3924_);
    v___x_3926_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3926_, 0, v_env_3921_);
    lean_ctor_set(v___x_3926_, 1, v_mctx_3923_);
    lean_ctor_set(v___x_3926_, 2, v_lctx_3924_);
    lean_ctor_set(v___x_3926_, 3, v_options_3925_);
    v___x_3927_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3927_, 0, v___x_3926_);
    lean_ctor_set(v___x_3927_, 1, v_msgData_3914_);
    v___x_3928_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3928_, 0, v___x_3927_);
    return v___x_3928_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1___boxed(
    mut v_msgData_3929_: *mut LeanObject,
    mut v___y_3930_: *mut LeanObject,
    mut v___y_3931_: *mut LeanObject,
    mut v___y_3932_: *mut LeanObject,
    mut v___y_3933_: *mut LeanObject,
    mut v___y_3934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3935_: *mut LeanObject = core::ptr::null_mut();
    v_res_3935_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msgData_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
    lean_dec(v___y_3933_);
    lean_dec_ref(v___y_3932_);
    lean_dec(v___y_3931_);
    lean_dec_ref(v___y_3930_);
    return v_res_3935_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(
    mut v_msg_3936_: *mut LeanObject,
    mut v___y_3937_: *mut LeanObject,
    mut v___y_3938_: *mut LeanObject,
    mut v___y_3939_: *mut LeanObject,
    mut v___y_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3947_: u8 = 0;
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3942_ = lean_ctor_get(v___y_3939_, 5);
                v___x_3943_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
                v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
                v_isSharedCheck_3952_ = (!lean_is_exclusive(v___x_3943_)) as u8;
                if v_isSharedCheck_3952_ == 0 {
                    v___x_3946_ = v___x_3943_;
                    v_isShared_3947_ = v_isSharedCheck_3952_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3944_);
                    lean_dec(v___x_3943_);
                    v___x_3946_ = lean_box(0);
                    v_isShared_3947_ = v_isSharedCheck_3952_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3942_);
                v___x_3948_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3948_, 0, v_ref_3942_);
                lean_ctor_set(v___x_3948_, 1, v_a_3944_);
                if v_isShared_3947_ == 0 {
                    lean_ctor_set_tag(v___x_3946_, 1);
                    lean_ctor_set(v___x_3946_, 0, v___x_3948_);
                    v___x_3950_ = v___x_3946_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3948_);
                    v___x_3950_ = v_reuseFailAlloc_3951_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg___boxed(
    mut v_msg_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
    mut v___y_3956_: *mut LeanObject,
    mut v___y_3957_: *mut LeanObject,
    mut v___y_3958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3959_: *mut LeanObject = core::ptr::null_mut();
    v_res_3959_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
    lean_dec(v___y_3957_);
    lean_dec_ref(v___y_3956_);
    lean_dec(v___y_3955_);
    lean_dec_ref(v___y_3954_);
    return v_res_3959_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(
    mut v_e_3960_: *mut LeanObject,
    mut v_a_3961_: u8,
    mut v_as_3962_: *mut LeanObject,
    mut v_sz_3963_: usize,
    mut v_i_3964_: usize,
    mut v_b_3965_: u8,
    mut v___y_3966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3976_: u8 = 0;
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: usize = 0;
    let mut v___x_3979_: usize = 0;
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3985_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3968_ = lean_usize_dec_lt(v_i_3964_, v_sz_3963_);
                if v___x_3968_ == 0 {
                    v___x_3969_ = lean_box((v_b_3965_) as usize);
                    v___x_3970_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3970_, 0, v___x_3969_);
                    return v___x_3970_;
                } else {
                    v_a_3971_ = lean_array_uget_borrowed(v_as_3962_, v_i_3964_);
                    v___x_3972_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_3960_, v_a_3971_, v___y_3966_);
                    if lean_obj_tag(v___x_3972_) == 0 {
                        v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
                        v_isSharedCheck_3985_ = (!lean_is_exclusive(v___x_3972_)) as u8;
                        if v_isSharedCheck_3985_ == 0 {
                            v___x_3975_ = v___x_3972_;
                            v_isShared_3976_ = v_isSharedCheck_3985_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3973_);
                            lean_dec(v___x_3972_);
                            v___x_3975_ = lean_box(0);
                            v_isShared_3976_ = v_isSharedCheck_3985_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3972_;
                    }
                }
            }
            1 => {
                v___x_3977_ = (lean_unbox(v_a_3973_) as u8);
                lean_dec(v_a_3973_);
                if v___x_3977_ == 0 {
                    lean_del_object(v___x_3975_);
                    v___x_3978_ = 1usize;
                    v___x_3979_ = lean_usize_add(v_i_3964_, v___x_3978_);
                    v_i_3964_ = v___x_3979_;
                    state = 0;
                    continue;
                } else {
                    v___x_3981_ = lean_box((v_a_3961_) as usize);
                    if v_isShared_3976_ == 0 {
                        lean_ctor_set(v___x_3975_, 0, v___x_3981_);
                        v___x_3983_ = v___x_3975_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3984_, 0, v___x_3981_);
                        v___x_3983_ = v_reuseFailAlloc_3984_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3983_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg___boxed(
    mut v_e_3986_: *mut LeanObject,
    mut v_a_3987_: *mut LeanObject,
    mut v_as_3988_: *mut LeanObject,
    mut v_sz_3989_: *mut LeanObject,
    mut v_i_3990_: *mut LeanObject,
    mut v_b_3991_: *mut LeanObject,
    mut v___y_3992_: *mut LeanObject,
    mut v___y_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_66419__boxed_3994_: u8 = 0;
    let mut v_sz_boxed_3995_: usize = 0;
    let mut v_i_boxed_3996_: usize = 0;
    let mut v_b_boxed_3997_: u8 = 0;
    let mut v_res_3998_: *mut LeanObject = core::ptr::null_mut();
    v_a_66419__boxed_3994_ = (lean_unbox(v_a_3987_) as u8);
    v_sz_boxed_3995_ = lean_unbox_usize(v_sz_3989_);
    lean_dec(v_sz_3989_);
    v_i_boxed_3996_ = lean_unbox_usize(v_i_3990_);
    lean_dec(v_i_3990_);
    v_b_boxed_3997_ = (lean_unbox(v_b_3991_) as u8);
    v_res_3998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_3986_, v_a_66419__boxed_3994_, v_as_3988_, v_sz_boxed_3995_, v_i_boxed_3996_, v_b_boxed_3997_, v___y_3992_);
    lean_dec(v___y_3992_);
    lean_dec_ref(v_as_3988_);
    lean_dec_ref(v_e_3986_);
    return v_res_3998_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    v___x_4001_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__1;
    v___x_4002_ = lean_unsigned_to_nat(8);
    v___x_4003_ = lean_unsigned_to_nat(75);
    v___x_4004_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0;
    v___x_4005_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_4006_ = l_mkPanicMessageWithDecl(
        v___x_4005_,
        v___x_4004_,
        v___x_4003_,
        v___x_4002_,
        v___x_4001_,
    );
    return v___x_4006_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    v___x_4008_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__3;
    v___x_4009_ = lean_unsigned_to_nat(10);
    v___x_4010_ = lean_unsigned_to_nat(93);
    v___x_4011_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0;
    v___x_4012_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_4013_ = l_mkPanicMessageWithDecl(
        v___x_4012_,
        v___x_4011_,
        v___x_4010_,
        v___x_4009_,
        v___x_4008_,
    );
    return v___x_4013_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    v___x_4015_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__5;
    v___x_4016_ = l_Lean_stringToMessageData(v___x_4015_);
    return v___x_4016_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    v___x_4018_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__7;
    v___x_4019_ = l_Lean_stringToMessageData(v___x_4018_);
    return v___x_4019_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4021_: *mut LeanObject = core::ptr::null_mut();
    v___x_4020_ = lean_box(0);
    v_dummy_4021_ = l_Lean_Expr_sort___override(v___x_4020_);
    return v_dummy_4021_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(
    mut v_e_4022_: *mut LeanObject,
    mut v_a_4023_: u8,
    mut v_as_x27_4024_: *mut LeanObject,
    mut v_b_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
    mut v___y_4027_: *mut LeanObject,
    mut v___y_4028_: *mut LeanObject,
    mut v___y_4029_: *mut LeanObject,
    mut v___y_4030_: *mut LeanObject,
    mut v___y_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
    mut v___y_4034_: *mut LeanObject,
    mut v___y_4035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4045_: u8 = 0;
    let mut v_a_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut v_a_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4060_: u8 = 0;
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: u8 = 0;
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4084_: u8 = 0;
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4088_: u8 = 0;
    let mut v___y_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: u8 = 0;
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_4108_: u8 = 0;
    let mut v___y_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: u8 = 0;
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_4134_: u8 = 0;
    let mut v___y_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: u8 = 0;
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: u8 = 0;
    let mut v___y_4151_: u8 = 0;
    let mut v___x_4152_: u8 = 0;
    let mut v_dummy_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4159_: usize = 0;
    let mut v___x_4160_: usize = 0;
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: u8 = 0;
    let mut v___x_4168_: u8 = 0;
    let mut v_a_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: u8 = 0;
    let mut v_a_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4174_: u8 = 0;
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4178_: u8 = 0;
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: u8 = 0;
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4193_: u8 = 0;
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4197_: u8 = 0;
    let mut v___x_4199_: u8 = 0;
    let mut v___x_4200_: u8 = 0;
    let mut v_a_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4208_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4024_) == 0 {
                    lean_dec_ref(v_e_4022_);
                    v___x_4037_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4037_, 0, v_b_4025_);
                    return v___x_4037_;
                } else {
                    v_head_4038_ = lean_ctor_get(v_as_x27_4024_, 0);
                    v_tail_4039_ = lean_ctor_get(v_as_x27_4024_, 1);
                    lean_inc(v_head_4038_);
                    v___x_4061_ = l_Lean_Meta_Grind_useFunCC___redArg(
                        v_head_4038_,
                        v___y_4026_,
                        v___y_4032_,
                        v___y_4033_,
                        v___y_4034_,
                        v___y_4035_,
                    );
                    if lean_obj_tag(v___x_4061_) == 0 {
                        v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
                        lean_inc(v_a_4062_);
                        lean_dec_ref_known(v___x_4061_, 1);
                        v___x_4063_ = lean_box(0);
                        v___x_4199_ = l_Lean_Expr_isApp(v_head_4038_);
                        if v___x_4199_ == 0 {
                            lean_dec(v_a_4062_);
                            v___y_4151_ = v___x_4199_;
                            state = 12;
                            continue;
                        } else {
                            v___x_4200_ = (lean_unbox(v_a_4062_) as u8);
                            lean_dec(v_a_4062_);
                            v___y_4151_ = v___x_4200_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_4022_);
                        v_a_4201_ = lean_ctor_get(v___x_4061_, 0);
                        v_isSharedCheck_4208_ = (!lean_is_exclusive(v___x_4061_)) as u8;
                        if v_isSharedCheck_4208_ == 0 {
                            v___x_4203_ = v___x_4061_;
                            v_isShared_4204_ = v_isSharedCheck_4208_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_4201_);
                            lean_dec(v___x_4061_);
                            v___x_4203_ = lean_box(0);
                            v_isShared_4204_ = v_isSharedCheck_4208_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_4041_) == 0 {
                    v_a_4042_ = lean_ctor_get(v___y_4041_, 0);
                    v_isSharedCheck_4052_ = (!lean_is_exclusive(v___y_4041_)) as u8;
                    if v_isSharedCheck_4052_ == 0 {
                        v___x_4044_ = v___y_4041_;
                        v_isShared_4045_ = v_isSharedCheck_4052_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4042_);
                        lean_dec(v___y_4041_);
                        v___x_4044_ = lean_box(0);
                        v_isShared_4045_ = v_isSharedCheck_4052_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_4022_);
                    v_a_4053_ = lean_ctor_get(v___y_4041_, 0);
                    v_isSharedCheck_4060_ = (!lean_is_exclusive(v___y_4041_)) as u8;
                    if v_isSharedCheck_4060_ == 0 {
                        v___x_4055_ = v___y_4041_;
                        v_isShared_4056_ = v_isSharedCheck_4060_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4053_);
                        lean_dec(v___y_4041_);
                        v___x_4055_ = lean_box(0);
                        v_isShared_4056_ = v_isSharedCheck_4060_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4042_) == 0 {
                    lean_dec_ref(v_e_4022_);
                    v_a_4046_ = lean_ctor_get(v_a_4042_, 0);
                    lean_inc(v_a_4046_);
                    lean_dec_ref_known(v_a_4042_, 1);
                    if v_isShared_4045_ == 0 {
                        lean_ctor_set(v___x_4044_, 0, v_a_4046_);
                        v___x_4048_ = v___x_4044_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4046_);
                        v___x_4048_ = v_reuseFailAlloc_4049_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4044_);
                    v_a_4050_ = lean_ctor_get(v_a_4042_, 0);
                    lean_inc(v_a_4050_);
                    lean_dec_ref_known(v_a_4042_, 1);
                    v_as_x27_4024_ = v_tail_4039_;
                    v_b_4025_ = v_a_4050_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_4048_;
            }
            4 => {
                if v_isShared_4056_ == 0 {
                    v___x_4058_ = v___x_4055_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
                    v___x_4058_ = v_reuseFailAlloc_4059_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4058_;
            }
            6 => {
                lean_inc(v_head_4038_);
                v___x_4075_ =
                    l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(
                        v_e_4022_,
                        v_head_4038_,
                        v___y_4065_,
                        v___y_4066_,
                        v___y_4067_,
                        v___y_4068_,
                        v___y_4069_,
                        v___y_4070_,
                        v___y_4071_,
                        v___y_4072_,
                        v___y_4073_,
                        v___y_4074_,
                    );
                if lean_obj_tag(v___x_4075_) == 0 {
                    v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
                    lean_inc(v_a_4076_);
                    lean_dec_ref_known(v___x_4075_, 1);
                    v___x_4077_ = (lean_unbox(v_a_4076_) as u8);
                    lean_dec(v_a_4076_);
                    if v___x_4077_ == 0 {
                        v___x_4078_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__2);
                        v___x_4079_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_4078_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
                        v___y_4041_ = v___x_4079_;
                        state = 1;
                        continue;
                    } else {
                        v_as_x27_4024_ = v_tail_4039_;
                        v_b_4025_ = v___x_4063_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_4022_);
                    v_a_4081_ = lean_ctor_get(v___x_4075_, 0);
                    v_isSharedCheck_4088_ = (!lean_is_exclusive(v___x_4075_)) as u8;
                    if v_isSharedCheck_4088_ == 0 {
                        v___x_4083_ = v___x_4075_;
                        v_isShared_4084_ = v_isSharedCheck_4088_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4081_);
                        lean_dec(v___x_4075_);
                        v___x_4083_ = lean_box(0);
                        v_isShared_4084_ = v_isSharedCheck_4088_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_4084_ == 0 {
                    v___x_4086_ = v___x_4083_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
                    v___x_4086_ = v_reuseFailAlloc_4087_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4086_;
            }
            9 => {
                v___x_4101_ =
                    l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(
                        v_e_4022_,
                        v___y_4090_,
                        v___y_4091_,
                    );
                lean_dec_ref(v___y_4090_);
                v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
                lean_inc(v_a_4102_);
                lean_dec_ref(v___x_4101_);
                v___x_4103_ = (lean_unbox(v_a_4102_) as u8);
                lean_dec(v_a_4102_);
                if v___x_4103_ == 0 {
                    v___x_4104_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__4);
                    v___x_4105_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_4104_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
                    v___y_4041_ = v___x_4105_;
                    state = 1;
                    continue;
                } else {
                    v_as_x27_4024_ = v_tail_4039_;
                    v_b_4025_ = v___x_4063_;
                    state = 0;
                    continue;
                }
            }
            10 => {
                if v_found_4108_ == 0 {
                    v___x_4119_ = l_Lean_Expr_getAppFn(v_head_4038_);
                    v___x_4120_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_4022_, v___x_4119_, v___y_4109_);
                    v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
                    lean_inc(v_a_4121_);
                    lean_dec_ref(v___x_4120_);
                    v___x_4122_ = (lean_unbox(v_a_4121_) as u8);
                    lean_dec(v_a_4121_);
                    if v___x_4122_ == 0 {
                        lean_dec_ref(v___x_4119_);
                        v___x_4123_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
                        v___x_4124_ = l_Lean_MessageData_ofExpr(v_e_4022_);
                        v___x_4125_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4125_, 0, v___x_4123_);
                        lean_ctor_set(v___x_4125_, 1, v___x_4124_);
                        v___x_4126_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8);
                        v___x_4127_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4127_, 0, v___x_4125_);
                        lean_ctor_set(v___x_4127_, 1, v___x_4126_);
                        lean_inc(v_head_4038_);
                        v___x_4128_ = l_Lean_MessageData_ofExpr(v_head_4038_);
                        v___x_4129_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4129_, 0, v___x_4127_);
                        lean_ctor_set(v___x_4129_, 1, v___x_4128_);
                        v___x_4130_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_4129_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
                        return v___x_4130_;
                    } else {
                        v___y_4090_ = v___x_4119_;
                        v___y_4091_ = v___y_4109_;
                        v___y_4092_ = v___y_4110_;
                        v___y_4093_ = v___y_4111_;
                        v___y_4094_ = v___y_4112_;
                        v___y_4095_ = v___y_4113_;
                        v___y_4096_ = v___y_4114_;
                        v___y_4097_ = v___y_4115_;
                        v___y_4098_ = v___y_4116_;
                        v___y_4099_ = v___y_4117_;
                        v___y_4100_ = v___y_4118_;
                        state = 9;
                        continue;
                    }
                } else {
                    v_as_x27_4024_ = v_tail_4039_;
                    v_b_4025_ = v___x_4063_;
                    state = 0;
                    continue;
                }
            }
            11 => {
                v___x_4145_ = l_Lean_Expr_hasLooseBVars(v___y_4133_);
                if v___x_4145_ == 0 {
                    v___x_4146_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_4022_, v___y_4133_, v___y_4135_);
                    lean_dec_ref(v___y_4133_);
                    v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
                    lean_inc(v_a_4147_);
                    lean_dec_ref(v___x_4146_);
                    v___x_4148_ = (lean_unbox(v_a_4147_) as u8);
                    lean_dec(v_a_4147_);
                    if v___x_4148_ == 0 {
                        v_found_4108_ = v_found_4134_;
                        v___y_4109_ = v___y_4135_;
                        v___y_4110_ = v___y_4136_;
                        v___y_4111_ = v___y_4137_;
                        v___y_4112_ = v___y_4138_;
                        v___y_4113_ = v___y_4139_;
                        v___y_4114_ = v___y_4140_;
                        v___y_4115_ = v___y_4141_;
                        v___y_4116_ = v___y_4142_;
                        v___y_4117_ = v___y_4143_;
                        v___y_4118_ = v___y_4144_;
                        state = 10;
                        continue;
                    } else {
                        v_as_x27_4024_ = v_tail_4039_;
                        v_b_4025_ = v___x_4063_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_4133_);
                    v_found_4108_ = v_found_4134_;
                    v___y_4109_ = v___y_4135_;
                    v___y_4110_ = v___y_4136_;
                    v___y_4111_ = v___y_4137_;
                    v___y_4112_ = v___y_4138_;
                    v___y_4113_ = v___y_4139_;
                    v___y_4114_ = v___y_4140_;
                    v___y_4115_ = v___y_4141_;
                    v___y_4116_ = v___y_4142_;
                    v___y_4117_ = v___y_4143_;
                    v___y_4118_ = v___y_4144_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                if v___y_4151_ == 0 {
                    v___x_4152_ = l_Lean_Meta_Grind_isMatchCond(v_head_4038_);
                    if v___x_4152_ == 0 {
                        v_dummy_4153_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__9);
                        v_nargs_4154_ = l_Lean_Expr_getAppNumArgs(v_head_4038_);
                        lean_inc(v_nargs_4154_);
                        v___x_4155_ = lean_mk_array(v_nargs_4154_, v_dummy_4153_);
                        v___x_4156_ = lean_unsigned_to_nat(1);
                        v___x_4157_ = lean_nat_sub(v_nargs_4154_, v___x_4156_);
                        lean_dec(v_nargs_4154_);
                        lean_inc(v_head_4038_);
                        v___x_4158_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v_head_4038_,
                            v___x_4155_,
                            v___x_4157_,
                        );
                        v_sz_4159_ = lean_array_size(v___x_4158_);
                        v___x_4160_ = 0usize;
                        v___x_4161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_4022_, v_a_4023_, v___x_4158_, v_sz_4159_, v___x_4160_, v___x_4152_, v___y_4026_);
                        lean_dec_ref(v___x_4158_);
                        if lean_obj_tag(v___x_4161_) == 0 {
                            if lean_obj_tag(v_head_4038_) == 7 {
                                v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
                                lean_inc(v_a_4162_);
                                lean_dec_ref_known(v___x_4161_, 1);
                                v_binderType_4163_ = lean_ctor_get(v_head_4038_, 1);
                                v_body_4164_ = lean_ctor_get(v_head_4038_, 2);
                                v___x_4165_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkChild___redArg(v_e_4022_, v_binderType_4163_, v___y_4026_);
                                v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
                                lean_inc(v_a_4166_);
                                lean_dec_ref(v___x_4165_);
                                v___x_4167_ = (lean_unbox(v_a_4166_) as u8);
                                lean_dec(v_a_4166_);
                                if v___x_4167_ == 0 {
                                    v___x_4168_ = (lean_unbox(v_a_4162_) as u8);
                                    lean_dec(v_a_4162_);
                                    lean_inc_ref(v_body_4164_);
                                    v___y_4133_ = v_body_4164_;
                                    v_found_4134_ = v___x_4168_;
                                    v___y_4135_ = v___y_4026_;
                                    v___y_4136_ = v___y_4027_;
                                    v___y_4137_ = v___y_4028_;
                                    v___y_4138_ = v___y_4029_;
                                    v___y_4139_ = v___y_4030_;
                                    v___y_4140_ = v___y_4031_;
                                    v___y_4141_ = v___y_4032_;
                                    v___y_4142_ = v___y_4033_;
                                    v___y_4143_ = v___y_4034_;
                                    v___y_4144_ = v___y_4035_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_dec(v_a_4162_);
                                    lean_inc_ref(v_body_4164_);
                                    v___y_4133_ = v_body_4164_;
                                    v_found_4134_ = v_a_4023_;
                                    v___y_4135_ = v___y_4026_;
                                    v___y_4136_ = v___y_4027_;
                                    v___y_4137_ = v___y_4028_;
                                    v___y_4138_ = v___y_4029_;
                                    v___y_4139_ = v___y_4030_;
                                    v___y_4140_ = v___y_4031_;
                                    v___y_4141_ = v___y_4032_;
                                    v___y_4142_ = v___y_4033_;
                                    v___y_4143_ = v___y_4034_;
                                    v___y_4144_ = v___y_4035_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                v_a_4169_ = lean_ctor_get(v___x_4161_, 0);
                                lean_inc(v_a_4169_);
                                lean_dec_ref_known(v___x_4161_, 1);
                                v___x_4170_ = (lean_unbox(v_a_4169_) as u8);
                                lean_dec(v_a_4169_);
                                v_found_4108_ = v___x_4170_;
                                v___y_4109_ = v___y_4026_;
                                v___y_4110_ = v___y_4027_;
                                v___y_4111_ = v___y_4028_;
                                v___y_4112_ = v___y_4029_;
                                v___y_4113_ = v___y_4030_;
                                v___y_4114_ = v___y_4031_;
                                v___y_4115_ = v___y_4032_;
                                v___y_4116_ = v___y_4033_;
                                v___y_4117_ = v___y_4034_;
                                v___y_4118_ = v___y_4035_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_e_4022_);
                            v_a_4171_ = lean_ctor_get(v___x_4161_, 0);
                            v_isSharedCheck_4178_ = (!lean_is_exclusive(v___x_4161_)) as u8;
                            if v_isSharedCheck_4178_ == 0 {
                                v___x_4173_ = v___x_4161_;
                                v_isShared_4174_ = v_isSharedCheck_4178_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_4171_);
                                lean_dec(v___x_4161_);
                                v___x_4173_ = lean_box(0);
                                v_isShared_4174_ = v_isSharedCheck_4178_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_inc(v_head_4038_);
                        v___x_4179_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkMatchCondParent(v_e_4022_, v_head_4038_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
                        if lean_obj_tag(v___x_4179_) == 0 {
                            v_a_4180_ = lean_ctor_get(v___x_4179_, 0);
                            lean_inc(v_a_4180_);
                            lean_dec_ref_known(v___x_4179_, 1);
                            v___x_4181_ = (lean_unbox(v_a_4180_) as u8);
                            lean_dec(v_a_4180_);
                            if v___x_4181_ == 0 {
                                v___x_4182_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__6);
                                v___x_4183_ = l_Lean_MessageData_ofExpr(v_e_4022_);
                                v___x_4184_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4184_, 0, v___x_4182_);
                                lean_ctor_set(v___x_4184_, 1, v___x_4183_);
                                v___x_4185_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__8);
                                v___x_4186_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4186_, 0, v___x_4184_);
                                lean_ctor_set(v___x_4186_, 1, v___x_4185_);
                                lean_inc(v_head_4038_);
                                v___x_4187_ = l_Lean_MessageData_ofExpr(v_head_4038_);
                                v___x_4188_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4188_, 0, v___x_4186_);
                                lean_ctor_set(v___x_4188_, 1, v___x_4187_);
                                v___x_4189_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v___x_4188_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
                                return v___x_4189_;
                            } else {
                                v___y_4065_ = v___y_4026_;
                                v___y_4066_ = v___y_4027_;
                                v___y_4067_ = v___y_4028_;
                                v___y_4068_ = v___y_4029_;
                                v___y_4069_ = v___y_4030_;
                                v___y_4070_ = v___y_4031_;
                                v___y_4071_ = v___y_4032_;
                                v___y_4072_ = v___y_4033_;
                                v___y_4073_ = v___y_4034_;
                                v___y_4074_ = v___y_4035_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_e_4022_);
                            v_a_4190_ = lean_ctor_get(v___x_4179_, 0);
                            v_isSharedCheck_4197_ = (!lean_is_exclusive(v___x_4179_)) as u8;
                            if v_isSharedCheck_4197_ == 0 {
                                v___x_4192_ = v___x_4179_;
                                v_isShared_4193_ = v_isSharedCheck_4197_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_4190_);
                                lean_dec(v___x_4179_);
                                v___x_4192_ = lean_box(0);
                                v_isShared_4193_ = v_isSharedCheck_4197_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    v_as_x27_4024_ = v_tail_4039_;
                    v_b_4025_ = v___x_4063_;
                    state = 0;
                    continue;
                }
            }
            13 => {
                if v_isShared_4174_ == 0 {
                    v___x_4176_ = v___x_4173_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4171_);
                    v___x_4176_ = v_reuseFailAlloc_4177_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4176_;
            }
            15 => {
                if v_isShared_4193_ == 0 {
                    v___x_4195_ = v___x_4192_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
                    v___x_4195_ = v_reuseFailAlloc_4196_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4195_;
            }
            17 => {
                if v_isShared_4204_ == 0 {
                    v___x_4206_ = v___x_4203_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
                    v___x_4206_ = v_reuseFailAlloc_4207_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4206_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___boxed(
    mut v_e_4209_: *mut LeanObject,
    mut v_a_4210_: *mut LeanObject,
    mut v_as_x27_4211_: *mut LeanObject,
    mut v_b_4212_: *mut LeanObject,
    mut v___y_4213_: *mut LeanObject,
    mut v___y_4214_: *mut LeanObject,
    mut v___y_4215_: *mut LeanObject,
    mut v___y_4216_: *mut LeanObject,
    mut v___y_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
    mut v___y_4220_: *mut LeanObject,
    mut v___y_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
    mut v___y_4223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_66516__boxed_4224_: u8 = 0;
    let mut v_res_4225_: *mut LeanObject = core::ptr::null_mut();
    v_a_66516__boxed_4224_ = (lean_unbox(v_a_4210_) as u8);
    v_res_4225_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_4209_, v_a_66516__boxed_4224_, v_as_x27_4211_, v_b_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
    lean_dec(v___y_4222_);
    lean_dec_ref(v___y_4221_);
    lean_dec(v___y_4220_);
    lean_dec_ref(v___y_4219_);
    lean_dec(v___y_4218_);
    lean_dec_ref(v___y_4217_);
    lean_dec(v___y_4216_);
    lean_dec_ref(v___y_4215_);
    lean_dec(v___y_4214_);
    lean_dec(v___y_4213_);
    lean_dec(v_as_x27_4211_);
    return v_res_4225_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1()
-> *mut LeanObject {
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    v___x_4227_ =
        l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__0;
    v___x_4228_ = lean_unsigned_to_nat(6);
    v___x_4229_ = lean_unsigned_to_nat(96);
    v___x_4230_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg___closed__0;
    v___x_4231_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_4232_ = l_mkPanicMessageWithDecl(
        v___x_4231_,
        v___x_4230_,
        v___x_4229_,
        v___x_4228_,
        v___x_4227_,
    );
    return v___x_4232_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(
    mut v_e_4233_: *mut LeanObject,
    mut v_a_4234_: *mut LeanObject,
    mut v_a_4235_: *mut LeanObject,
    mut v_a_4236_: *mut LeanObject,
    mut v_a_4237_: *mut LeanObject,
    mut v_a_4238_: *mut LeanObject,
    mut v_a_4239_: *mut LeanObject,
    mut v_a_4240_: *mut LeanObject,
    mut v_a_4241_: *mut LeanObject,
    mut v_a_4242_: *mut LeanObject,
    mut v_a_4243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: u8 = 0;
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4252_: u8 = 0;
    let mut v___x_4253_: u8 = 0;
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4260_: u8 = 0;
    let mut v_a_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4264_: u8 = 0;
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4268_: u8 = 0;
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: u8 = 0;
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4281_: u8 = 0;
    let mut v_unused_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4286_: u8 = 0;
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4290_: u8 = 0;
    let mut v_a_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4294_: u8 = 0;
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4245_ = l_Lean_Meta_Grind_isRoot___redArg(v_e_4233_, v_a_4234_);
                if lean_obj_tag(v___x_4245_) == 0 {
                    v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
                    lean_inc(v_a_4246_);
                    lean_dec_ref_known(v___x_4245_, 1);
                    v___x_4247_ = (lean_unbox(v_a_4246_) as u8);
                    if v___x_4247_ == 0 {
                        lean_dec(v_a_4246_);
                        v___x_4248_ = l_Lean_Meta_Grind_getParents___redArg(v_e_4233_, v_a_4234_);
                        lean_dec_ref(v_e_4233_);
                        if lean_obj_tag(v___x_4248_) == 0 {
                            v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
                            v_isSharedCheck_4260_ = (!lean_is_exclusive(v___x_4248_)) as u8;
                            if v_isSharedCheck_4260_ == 0 {
                                v___x_4251_ = v___x_4248_;
                                v_isShared_4252_ = v_isSharedCheck_4260_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_4249_);
                                lean_dec(v___x_4248_);
                                v___x_4251_ = lean_box(0);
                                v_isShared_4252_ = v_isSharedCheck_4260_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4261_ = lean_ctor_get(v___x_4248_, 0);
                            v_isSharedCheck_4268_ = (!lean_is_exclusive(v___x_4248_)) as u8;
                            if v_isSharedCheck_4268_ == 0 {
                                v___x_4263_ = v___x_4248_;
                                v_isShared_4264_ = v_isSharedCheck_4268_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4261_);
                                lean_dec(v___x_4248_);
                                v___x_4263_ = lean_box(0);
                                v_isShared_4264_ = v_isSharedCheck_4268_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_4269_ = l_Lean_Meta_Grind_getParents___redArg(v_e_4233_, v_a_4234_);
                        if lean_obj_tag(v___x_4269_) == 0 {
                            v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
                            lean_inc(v_a_4270_);
                            lean_dec_ref_known(v___x_4269_, 1);
                            v___x_4271_ = l_Lean_Meta_Grind_ParentSet_elems(v_a_4270_);
                            lean_dec(v_a_4270_);
                            v___x_4272_ = lean_box(0);
                            v___x_4273_ = (lean_unbox(v_a_4246_) as u8);
                            lean_dec(v_a_4246_);
                            v___x_4274_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_4233_, v___x_4273_, v___x_4271_, v___x_4272_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
                            lean_dec(v___x_4271_);
                            if lean_obj_tag(v___x_4274_) == 0 {
                                v_isSharedCheck_4281_ = (!lean_is_exclusive(v___x_4274_)) as u8;
                                if v_isSharedCheck_4281_ == 0 {
                                    v_unused_4282_ = lean_ctor_get(v___x_4274_, 0);
                                    lean_dec(v_unused_4282_);
                                    v___x_4276_ = v___x_4274_;
                                    v_isShared_4277_ = v_isSharedCheck_4281_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec(v___x_4274_);
                                    v___x_4276_ = lean_box(0);
                                    v_isShared_4277_ = v_isSharedCheck_4281_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                return v___x_4274_;
                            }
                        } else {
                            lean_dec(v_a_4246_);
                            lean_dec_ref(v_e_4233_);
                            v_a_4283_ = lean_ctor_get(v___x_4269_, 0);
                            v_isSharedCheck_4290_ = (!lean_is_exclusive(v___x_4269_)) as u8;
                            if v_isSharedCheck_4290_ == 0 {
                                v___x_4285_ = v___x_4269_;
                                v_isShared_4286_ = v_isSharedCheck_4290_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4283_);
                                lean_dec(v___x_4269_);
                                v___x_4285_ = lean_box(0);
                                v_isShared_4286_ = v_isSharedCheck_4290_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_4233_);
                    v_a_4291_ = lean_ctor_get(v___x_4245_, 0);
                    v_isSharedCheck_4298_ = (!lean_is_exclusive(v___x_4245_)) as u8;
                    if v_isSharedCheck_4298_ == 0 {
                        v___x_4293_ = v___x_4245_;
                        v_isShared_4294_ = v_isSharedCheck_4298_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4291_);
                        lean_dec(v___x_4245_);
                        v___x_4293_ = lean_box(0);
                        v_isShared_4294_ = v_isSharedCheck_4298_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4253_ = l_Lean_Meta_Grind_ParentSet_isEmpty(v_a_4249_);
                lean_dec(v_a_4249_);
                if v___x_4253_ == 0 {
                    lean_del_object(v___x_4251_);
                    v___x_4254_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___closed__1);
                    v___x_4255_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__4(v___x_4254_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
                    return v___x_4255_;
                } else {
                    v___x_4256_ = lean_box(0);
                    if v_isShared_4252_ == 0 {
                        lean_ctor_set(v___x_4251_, 0, v___x_4256_);
                        v___x_4258_ = v___x_4251_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
                        v___x_4258_ = v_reuseFailAlloc_4259_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4258_;
            }
            3 => {
                if v_isShared_4264_ == 0 {
                    v___x_4266_ = v___x_4263_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
                    v___x_4266_ = v_reuseFailAlloc_4267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4266_;
            }
            5 => {
                if v_isShared_4277_ == 0 {
                    lean_ctor_set(v___x_4276_, 0, v___x_4272_);
                    v___x_4279_ = v___x_4276_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4272_);
                    v___x_4279_ = v_reuseFailAlloc_4280_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4279_;
            }
            7 => {
                if v_isShared_4286_ == 0 {
                    v___x_4288_ = v___x_4285_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
                    v___x_4288_ = v_reuseFailAlloc_4289_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4288_;
            }
            9 => {
                if v_isShared_4294_ == 0 {
                    v___x_4296_ = v___x_4293_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
                    v___x_4296_ = v_reuseFailAlloc_4297_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents___boxed(
    mut v_e_4299_: *mut LeanObject,
    mut v_a_4300_: *mut LeanObject,
    mut v_a_4301_: *mut LeanObject,
    mut v_a_4302_: *mut LeanObject,
    mut v_a_4303_: *mut LeanObject,
    mut v_a_4304_: *mut LeanObject,
    mut v_a_4305_: *mut LeanObject,
    mut v_a_4306_: *mut LeanObject,
    mut v_a_4307_: *mut LeanObject,
    mut v_a_4308_: *mut LeanObject,
    mut v_a_4309_: *mut LeanObject,
    mut v_a_4310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4311_: *mut LeanObject = core::ptr::null_mut();
    v_res_4311_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(
        v_e_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_, v_a_4305_, v_a_4306_,
        v_a_4307_, v_a_4308_, v_a_4309_,
    );
    lean_dec(v_a_4309_);
    lean_dec_ref(v_a_4308_);
    lean_dec(v_a_4307_);
    lean_dec_ref(v_a_4306_);
    lean_dec(v_a_4305_);
    lean_dec_ref(v_a_4304_);
    lean_dec(v_a_4303_);
    lean_dec_ref(v_a_4302_);
    lean_dec(v_a_4301_);
    lean_dec(v_a_4300_);
    return v_res_4311_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(
    mut v_00_u03b1_4312_: *mut LeanObject,
    mut v_msg_4313_: *mut LeanObject,
    mut v___y_4314_: *mut LeanObject,
    mut v___y_4315_: *mut LeanObject,
    mut v___y_4316_: *mut LeanObject,
    mut v___y_4317_: *mut LeanObject,
    mut v___y_4318_: *mut LeanObject,
    mut v___y_4319_: *mut LeanObject,
    mut v___y_4320_: *mut LeanObject,
    mut v___y_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    v___x_4325_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___redArg(v_msg_4313_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
    return v___x_4325_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1___boxed(
    mut v_00_u03b1_4326_: *mut LeanObject,
    mut v_msg_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
    mut v___y_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
    mut v___y_4332_: *mut LeanObject,
    mut v___y_4333_: *mut LeanObject,
    mut v___y_4334_: *mut LeanObject,
    mut v___y_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4339_: *mut LeanObject = core::ptr::null_mut();
    v_res_4339_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1(v_00_u03b1_4326_, v_msg_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
    lean_dec(v___y_4337_);
    lean_dec_ref(v___y_4336_);
    lean_dec(v___y_4335_);
    lean_dec_ref(v___y_4334_);
    lean_dec(v___y_4333_);
    lean_dec_ref(v___y_4332_);
    lean_dec(v___y_4331_);
    lean_dec_ref(v___y_4330_);
    lean_dec(v___y_4329_);
    lean_dec(v___y_4328_);
    return v_res_4339_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(
    mut v_e_4340_: *mut LeanObject,
    mut v_a_4341_: u8,
    mut v_as_4342_: *mut LeanObject,
    mut v_sz_4343_: usize,
    mut v_i_4344_: usize,
    mut v_b_4345_: u8,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
    mut v___y_4354_: *mut LeanObject,
    mut v___y_4355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    v___x_4357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___redArg(v_e_4340_, v_a_4341_, v_as_4342_, v_sz_4343_, v_i_4344_, v_b_4345_, v___y_4346_);
    return v___x_4357_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_4358_: *mut LeanObject = *_args.add(0);
    let mut v_a_4359_: *mut LeanObject = *_args.add(1);
    let mut v_as_4360_: *mut LeanObject = *_args.add(2);
    let mut v_sz_4361_: *mut LeanObject = *_args.add(3);
    let mut v_i_4362_: *mut LeanObject = *_args.add(4);
    let mut v_b_4363_: *mut LeanObject = *_args.add(5);
    let mut v___y_4364_: *mut LeanObject = *_args.add(6);
    let mut v___y_4365_: *mut LeanObject = *_args.add(7);
    let mut v___y_4366_: *mut LeanObject = *_args.add(8);
    let mut v___y_4367_: *mut LeanObject = *_args.add(9);
    let mut v___y_4368_: *mut LeanObject = *_args.add(10);
    let mut v___y_4369_: *mut LeanObject = *_args.add(11);
    let mut v___y_4370_: *mut LeanObject = *_args.add(12);
    let mut v___y_4371_: *mut LeanObject = *_args.add(13);
    let mut v___y_4372_: *mut LeanObject = *_args.add(14);
    let mut v___y_4373_: *mut LeanObject = *_args.add(15);
    let mut v___y_4374_: *mut LeanObject = *_args.add(16);
    let mut v_a_67089__boxed_4375_: u8 = 0;
    let mut v_sz_boxed_4376_: usize = 0;
    let mut v_i_boxed_4377_: usize = 0;
    let mut v_b_boxed_4378_: u8 = 0;
    let mut v_res_4379_: *mut LeanObject = core::ptr::null_mut();
    v_a_67089__boxed_4375_ = (lean_unbox(v_a_4359_) as u8);
    v_sz_boxed_4376_ = lean_unbox_usize(v_sz_4361_);
    lean_dec(v_sz_4361_);
    v_i_boxed_4377_ = lean_unbox_usize(v_i_4362_);
    lean_dec(v_i_4362_);
    v_b_boxed_4378_ = (lean_unbox(v_b_4363_) as u8);
    v_res_4379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__2(v_e_4358_, v_a_67089__boxed_4375_, v_as_4360_, v_sz_boxed_4376_, v_i_boxed_4377_, v_b_boxed_4378_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
    lean_dec(v___y_4373_);
    lean_dec_ref(v___y_4372_);
    lean_dec(v___y_4371_);
    lean_dec_ref(v___y_4370_);
    lean_dec(v___y_4369_);
    lean_dec_ref(v___y_4368_);
    lean_dec(v___y_4367_);
    lean_dec_ref(v___y_4366_);
    lean_dec(v___y_4365_);
    lean_dec(v___y_4364_);
    lean_dec_ref(v_as_4360_);
    lean_dec_ref(v_e_4358_);
    return v_res_4379_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(
    mut v_e_4380_: *mut LeanObject,
    mut v_a_4381_: u8,
    mut v_as_4382_: *mut LeanObject,
    mut v_as_x27_4383_: *mut LeanObject,
    mut v_b_4384_: *mut LeanObject,
    mut v_a_4385_: *mut LeanObject,
    mut v___y_4386_: *mut LeanObject,
    mut v___y_4387_: *mut LeanObject,
    mut v___y_4388_: *mut LeanObject,
    mut v___y_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    v___x_4397_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___redArg(v_e_4380_, v_a_4381_, v_as_x27_4383_, v_b_4384_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
    return v___x_4397_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_4398_: *mut LeanObject = *_args.add(0);
    let mut v_a_4399_: *mut LeanObject = *_args.add(1);
    let mut v_as_4400_: *mut LeanObject = *_args.add(2);
    let mut v_as_x27_4401_: *mut LeanObject = *_args.add(3);
    let mut v_b_4402_: *mut LeanObject = *_args.add(4);
    let mut v_a_4403_: *mut LeanObject = *_args.add(5);
    let mut v___y_4404_: *mut LeanObject = *_args.add(6);
    let mut v___y_4405_: *mut LeanObject = *_args.add(7);
    let mut v___y_4406_: *mut LeanObject = *_args.add(8);
    let mut v___y_4407_: *mut LeanObject = *_args.add(9);
    let mut v___y_4408_: *mut LeanObject = *_args.add(10);
    let mut v___y_4409_: *mut LeanObject = *_args.add(11);
    let mut v___y_4410_: *mut LeanObject = *_args.add(12);
    let mut v___y_4411_: *mut LeanObject = *_args.add(13);
    let mut v___y_4412_: *mut LeanObject = *_args.add(14);
    let mut v___y_4413_: *mut LeanObject = *_args.add(15);
    let mut v___y_4414_: *mut LeanObject = *_args.add(16);
    let mut v_a_67127__boxed_4415_: u8 = 0;
    let mut v_res_4416_: *mut LeanObject = core::ptr::null_mut();
    v_a_67127__boxed_4415_ = (lean_unbox(v_a_4399_) as u8);
    v_res_4416_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__3(v_e_4398_, v_a_67127__boxed_4415_, v_as_4400_, v_as_x27_4401_, v_b_4402_, v_a_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
    lean_dec(v___y_4413_);
    lean_dec_ref(v___y_4412_);
    lean_dec(v___y_4411_);
    lean_dec_ref(v___y_4410_);
    lean_dec(v___y_4409_);
    lean_dec_ref(v___y_4408_);
    lean_dec(v___y_4407_);
    lean_dec_ref(v___y_4406_);
    lean_dec(v___y_4405_);
    lean_dec(v___y_4404_);
    lean_dec(v_as_x27_4401_);
    lean_dec(v_as_4400_);
    return v_res_4416_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    v___x_4419_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__1;
    v___x_4420_ = lean_unsigned_to_nat(6);
    v___x_4421_ = lean_unsigned_to_nat(107);
    v___x_4422_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0;
    v___x_4423_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_4424_ = l_mkPanicMessageWithDecl(
        v___x_4423_,
        v___x_4422_,
        v___x_4421_,
        v___x_4420_,
        v___x_4419_,
    );
    return v___x_4424_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    v___x_4426_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__3;
    v___x_4427_ = lean_unsigned_to_nat(6);
    v___x_4428_ = lean_unsigned_to_nat(105);
    v___x_4429_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__0;
    v___x_4430_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc_spec__3___redArg___lam__0___closed__0;
    v___x_4431_ = l_mkPanicMessageWithDecl(
        v___x_4430_,
        v___x_4429_,
        v___x_4428_,
        v___x_4427_,
        v___x_4426_,
    );
    return v___x_4431_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(
    mut v_upperBound_4432_: *mut LeanObject,
    mut v_a_4433_: *mut LeanObject,
    mut v___x_4434_: *mut LeanObject,
    mut v_a_4435_: *mut LeanObject,
    mut v_b_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
    mut v___y_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v___y_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v_a_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4464_: u8 = 0;
    let mut v_a_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4472_: u8 = 0;
    let mut v___x_4473_: u8 = 0;
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: u8 = 0;
    let mut v___x_4478_: u8 = 0;
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4473_ = lean_nat_dec_lt(v_a_4435_, v_upperBound_4432_);
                if v___x_4473_ == 0 {
                    lean_dec(v_a_4435_);
                    v___x_4474_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4474_, 0, v_b_4436_);
                    return v___x_4474_;
                } else {
                    v___x_4475_ = l_Lean_instInhabitedExpr;
                    v___x_4476_ =
                        l_Lean_PersistentArray_get_x21___redArg(v___x_4475_, v_a_4433_, v_a_4435_);
                    v___x_4477_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v___x_4434_,
                            v___x_4476_,
                        );
                    if v___x_4477_ == 0 {
                        v___x_4478_ = lean_expr_equal(v___x_4434_, v___x_4476_);
                        lean_dec(v___x_4476_);
                        if v___x_4478_ == 0 {
                            v___x_4479_ = lean_box(0);
                            v_a_4449_ = v___x_4479_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4480_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__2);
                            v___x_4481_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_4480_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
                            v___y_4454_ = v___x_4481_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4476_);
                        v___x_4482_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___closed__4);
                        v___x_4483_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__0(v___x_4482_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
                        v___y_4454_ = v___x_4483_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4450_ = lean_unsigned_to_nat(1);
                v___x_4451_ = lean_nat_add(v_a_4435_, v___x_4450_);
                lean_dec(v_a_4435_);
                v_a_4435_ = v___x_4451_;
                v_b_4436_ = v_a_4449_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_4454_) == 0 {
                    v_a_4455_ = lean_ctor_get(v___y_4454_, 0);
                    v_isSharedCheck_4464_ = (!lean_is_exclusive(v___y_4454_)) as u8;
                    if v_isSharedCheck_4464_ == 0 {
                        v___x_4457_ = v___y_4454_;
                        v_isShared_4458_ = v_isSharedCheck_4464_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4455_);
                        lean_dec(v___y_4454_);
                        v___x_4457_ = lean_box(0);
                        v_isShared_4458_ = v_isSharedCheck_4464_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4435_);
                    v_a_4465_ = lean_ctor_get(v___y_4454_, 0);
                    v_isSharedCheck_4472_ = (!lean_is_exclusive(v___y_4454_)) as u8;
                    if v_isSharedCheck_4472_ == 0 {
                        v___x_4467_ = v___y_4454_;
                        v_isShared_4468_ = v_isSharedCheck_4472_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4465_);
                        lean_dec(v___y_4454_);
                        v___x_4467_ = lean_box(0);
                        v_isShared_4468_ = v_isSharedCheck_4472_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_4455_) == 0 {
                    lean_dec(v_a_4435_);
                    v_a_4459_ = lean_ctor_get(v_a_4455_, 0);
                    lean_inc(v_a_4459_);
                    lean_dec_ref_known(v_a_4455_, 1);
                    if v_isShared_4458_ == 0 {
                        lean_ctor_set(v___x_4457_, 0, v_a_4459_);
                        v___x_4461_ = v___x_4457_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4462_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4462_, 0, v_a_4459_);
                        v___x_4461_ = v_reuseFailAlloc_4462_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4457_);
                    v_a_4463_ = lean_ctor_get(v_a_4455_, 0);
                    lean_inc(v_a_4463_);
                    lean_dec_ref_known(v_a_4455_, 1);
                    v_a_4449_ = v_a_4463_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                return v___x_4461_;
            }
            5 => {
                if v_isShared_4468_ == 0 {
                    v___x_4470_ = v___x_4467_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
                    v___x_4470_ = v_reuseFailAlloc_4471_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4470_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg___boxed(
    mut v_upperBound_4484_: *mut LeanObject,
    mut v_a_4485_: *mut LeanObject,
    mut v___x_4486_: *mut LeanObject,
    mut v_a_4487_: *mut LeanObject,
    mut v_b_4488_: *mut LeanObject,
    mut v___y_4489_: *mut LeanObject,
    mut v___y_4490_: *mut LeanObject,
    mut v___y_4491_: *mut LeanObject,
    mut v___y_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4500_: *mut LeanObject = core::ptr::null_mut();
    v_res_4500_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_4484_, v_a_4485_, v___x_4486_, v_a_4487_, v_b_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
    lean_dec(v___y_4498_);
    lean_dec_ref(v___y_4497_);
    lean_dec(v___y_4496_);
    lean_dec_ref(v___y_4495_);
    lean_dec(v___y_4494_);
    lean_dec_ref(v___y_4493_);
    lean_dec(v___y_4492_);
    lean_dec_ref(v___y_4491_);
    lean_dec(v___y_4490_);
    lean_dec(v___y_4489_);
    lean_dec_ref(v___x_4486_);
    lean_dec_ref(v_a_4485_);
    lean_dec(v_upperBound_4484_);
    return v_res_4500_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(
    mut v_upperBound_4501_: *mut LeanObject,
    mut v___x_4502_: *mut LeanObject,
    mut v_a_4503_: *mut LeanObject,
    mut v_a_4504_: *mut LeanObject,
    mut v_b_4505_: *mut LeanObject,
    mut v___y_4506_: *mut LeanObject,
    mut v___y_4507_: *mut LeanObject,
    mut v___y_4508_: *mut LeanObject,
    mut v___y_4509_: *mut LeanObject,
    mut v___y_4510_: *mut LeanObject,
    mut v___y_4511_: *mut LeanObject,
    mut v___y_4512_: *mut LeanObject,
    mut v___y_4513_: *mut LeanObject,
    mut v___y_4514_: *mut LeanObject,
    mut v___y_4515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4517_: u8 = 0;
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4517_ = lean_nat_dec_lt(v_a_4504_, v_upperBound_4501_);
                if v___x_4517_ == 0 {
                    lean_dec(v_a_4504_);
                    v___x_4518_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4518_, 0, v_b_4505_);
                    return v___x_4518_;
                } else {
                    v___x_4519_ = lean_box(0);
                    v___x_4520_ = l_Lean_instInhabitedExpr;
                    v___x_4521_ = lean_unsigned_to_nat(1);
                    v___x_4522_ = lean_nat_add(v_a_4504_, v___x_4521_);
                    v___x_4523_ =
                        l_Lean_PersistentArray_get_x21___redArg(v___x_4520_, v_a_4503_, v_a_4504_);
                    lean_dec(v_a_4504_);
                    lean_inc(v___x_4522_);
                    v___x_4524_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v___x_4502_, v_a_4503_, v___x_4523_, v___x_4522_, v___x_4519_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
                    lean_dec(v___x_4523_);
                    if lean_obj_tag(v___x_4524_) == 0 {
                        lean_dec_ref_known(v___x_4524_, 1);
                        v_a_4504_ = v___x_4522_;
                        v_b_4505_ = v___x_4519_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_4522_);
                        return v___x_4524_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg___boxed(
    mut v_upperBound_4526_: *mut LeanObject,
    mut v___x_4527_: *mut LeanObject,
    mut v_a_4528_: *mut LeanObject,
    mut v_a_4529_: *mut LeanObject,
    mut v_b_4530_: *mut LeanObject,
    mut v___y_4531_: *mut LeanObject,
    mut v___y_4532_: *mut LeanObject,
    mut v___y_4533_: *mut LeanObject,
    mut v___y_4534_: *mut LeanObject,
    mut v___y_4535_: *mut LeanObject,
    mut v___y_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
    mut v___y_4538_: *mut LeanObject,
    mut v___y_4539_: *mut LeanObject,
    mut v___y_4540_: *mut LeanObject,
    mut v___y_4541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4542_: *mut LeanObject = core::ptr::null_mut();
    v_res_4542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_4526_, v___x_4527_, v_a_4528_, v_a_4529_, v_b_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
    lean_dec(v___y_4540_);
    lean_dec_ref(v___y_4539_);
    lean_dec(v___y_4538_);
    lean_dec_ref(v___y_4537_);
    lean_dec(v___y_4536_);
    lean_dec_ref(v___y_4535_);
    lean_dec(v___y_4534_);
    lean_dec_ref(v___y_4533_);
    lean_dec(v___y_4532_);
    lean_dec(v___y_4531_);
    lean_dec_ref(v_a_4528_);
    lean_dec(v___x_4527_);
    lean_dec(v_upperBound_4526_);
    return v_res_4542_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(
    mut v_a_4543_: *mut LeanObject,
    mut v_a_4544_: *mut LeanObject,
    mut v_a_4545_: *mut LeanObject,
    mut v_a_4546_: *mut LeanObject,
    mut v_a_4547_: *mut LeanObject,
    mut v_a_4548_: *mut LeanObject,
    mut v_a_4549_: *mut LeanObject,
    mut v_a_4550_: *mut LeanObject,
    mut v_a_4551_: *mut LeanObject,
    mut v_a_4552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4562_: u8 = 0;
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4566_: u8 = 0;
    let mut v_unused_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4571_: u8 = 0;
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4575_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4554_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_4543_);
                if lean_obj_tag(v___x_4554_) == 0 {
                    v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
                    lean_inc(v_a_4555_);
                    lean_dec_ref_known(v___x_4554_, 1);
                    v_size_4556_ = lean_ctor_get(v_a_4555_, 2);
                    lean_inc(v_size_4556_);
                    v___x_4557_ = lean_unsigned_to_nat(0);
                    v___x_4558_ = lean_box(0);
                    v___x_4559_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_size_4556_, v_size_4556_, v_a_4555_, v___x_4557_, v___x_4558_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
                    lean_dec(v_a_4555_);
                    lean_dec(v_size_4556_);
                    if lean_obj_tag(v___x_4559_) == 0 {
                        v_isSharedCheck_4566_ = (!lean_is_exclusive(v___x_4559_)) as u8;
                        if v_isSharedCheck_4566_ == 0 {
                            v_unused_4567_ = lean_ctor_get(v___x_4559_, 0);
                            lean_dec(v_unused_4567_);
                            v___x_4561_ = v___x_4559_;
                            v_isShared_4562_ = v_isSharedCheck_4566_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_4559_);
                            v___x_4561_ = lean_box(0);
                            v_isShared_4562_ = v_isSharedCheck_4566_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_4559_;
                    }
                } else {
                    v_a_4568_ = lean_ctor_get(v___x_4554_, 0);
                    v_isSharedCheck_4575_ = (!lean_is_exclusive(v___x_4554_)) as u8;
                    if v_isSharedCheck_4575_ == 0 {
                        v___x_4570_ = v___x_4554_;
                        v_isShared_4571_ = v_isSharedCheck_4575_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4568_);
                        lean_dec(v___x_4554_);
                        v___x_4570_ = lean_box(0);
                        v_isShared_4571_ = v_isSharedCheck_4575_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4562_ == 0 {
                    lean_ctor_set(v___x_4561_, 0, v___x_4558_);
                    v___x_4564_ = v___x_4561_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4558_);
                    v___x_4564_ = v_reuseFailAlloc_4565_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4564_;
            }
            3 => {
                if v_isShared_4571_ == 0 {
                    v___x_4573_ = v___x_4570_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4574_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
                    v___x_4573_ = v_reuseFailAlloc_4574_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4573_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq___boxed(
    mut v_a_4576_: *mut LeanObject,
    mut v_a_4577_: *mut LeanObject,
    mut v_a_4578_: *mut LeanObject,
    mut v_a_4579_: *mut LeanObject,
    mut v_a_4580_: *mut LeanObject,
    mut v_a_4581_: *mut LeanObject,
    mut v_a_4582_: *mut LeanObject,
    mut v_a_4583_: *mut LeanObject,
    mut v_a_4584_: *mut LeanObject,
    mut v_a_4585_: *mut LeanObject,
    mut v_a_4586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4587_: *mut LeanObject = core::ptr::null_mut();
    v_res_4587_ =
        l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(
            v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_,
            v_a_4584_, v_a_4585_,
        );
    lean_dec(v_a_4585_);
    lean_dec_ref(v_a_4584_);
    lean_dec(v_a_4583_);
    lean_dec_ref(v_a_4582_);
    lean_dec(v_a_4581_);
    lean_dec_ref(v_a_4580_);
    lean_dec(v_a_4579_);
    lean_dec_ref(v_a_4578_);
    lean_dec(v_a_4577_);
    lean_dec(v_a_4576_);
    return v_res_4587_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(
    mut v_upperBound_4588_: *mut LeanObject,
    mut v_a_4589_: *mut LeanObject,
    mut v___x_4590_: *mut LeanObject,
    mut v_inst_4591_: *mut LeanObject,
    mut v_R_4592_: *mut LeanObject,
    mut v_a_4593_: *mut LeanObject,
    mut v_b_4594_: *mut LeanObject,
    mut v_c_4595_: *mut LeanObject,
    mut v___y_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
    mut v___y_4600_: *mut LeanObject,
    mut v___y_4601_: *mut LeanObject,
    mut v___y_4602_: *mut LeanObject,
    mut v___y_4603_: *mut LeanObject,
    mut v___y_4604_: *mut LeanObject,
    mut v___y_4605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    v___x_4607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___redArg(v_upperBound_4588_, v_a_4589_, v___x_4590_, v_a_4593_, v_b_4594_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
    return v___x_4607_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_4608_: *mut LeanObject = *_args.add(0);
    let mut v_a_4609_: *mut LeanObject = *_args.add(1);
    let mut v___x_4610_: *mut LeanObject = *_args.add(2);
    let mut v_inst_4611_: *mut LeanObject = *_args.add(3);
    let mut v_R_4612_: *mut LeanObject = *_args.add(4);
    let mut v_a_4613_: *mut LeanObject = *_args.add(5);
    let mut v_b_4614_: *mut LeanObject = *_args.add(6);
    let mut v_c_4615_: *mut LeanObject = *_args.add(7);
    let mut v___y_4616_: *mut LeanObject = *_args.add(8);
    let mut v___y_4617_: *mut LeanObject = *_args.add(9);
    let mut v___y_4618_: *mut LeanObject = *_args.add(10);
    let mut v___y_4619_: *mut LeanObject = *_args.add(11);
    let mut v___y_4620_: *mut LeanObject = *_args.add(12);
    let mut v___y_4621_: *mut LeanObject = *_args.add(13);
    let mut v___y_4622_: *mut LeanObject = *_args.add(14);
    let mut v___y_4623_: *mut LeanObject = *_args.add(15);
    let mut v___y_4624_: *mut LeanObject = *_args.add(16);
    let mut v___y_4625_: *mut LeanObject = *_args.add(17);
    let mut v___y_4626_: *mut LeanObject = *_args.add(18);
    let mut v_res_4627_: *mut LeanObject = core::ptr::null_mut();
    v_res_4627_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__0(v_upperBound_4608_, v_a_4609_, v___x_4610_, v_inst_4611_, v_R_4612_, v_a_4613_, v_b_4614_, v_c_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
    lean_dec(v___y_4625_);
    lean_dec_ref(v___y_4624_);
    lean_dec(v___y_4623_);
    lean_dec_ref(v___y_4622_);
    lean_dec(v___y_4621_);
    lean_dec_ref(v___y_4620_);
    lean_dec(v___y_4619_);
    lean_dec_ref(v___y_4618_);
    lean_dec(v___y_4617_);
    lean_dec(v___y_4616_);
    lean_dec_ref(v___x_4610_);
    lean_dec_ref(v_a_4609_);
    lean_dec(v_upperBound_4608_);
    return v_res_4627_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(
    mut v_upperBound_4628_: *mut LeanObject,
    mut v___x_4629_: *mut LeanObject,
    mut v_a_4630_: *mut LeanObject,
    mut v_inst_4631_: *mut LeanObject,
    mut v_R_4632_: *mut LeanObject,
    mut v_a_4633_: *mut LeanObject,
    mut v_b_4634_: *mut LeanObject,
    mut v_c_4635_: *mut LeanObject,
    mut v___y_4636_: *mut LeanObject,
    mut v___y_4637_: *mut LeanObject,
    mut v___y_4638_: *mut LeanObject,
    mut v___y_4639_: *mut LeanObject,
    mut v___y_4640_: *mut LeanObject,
    mut v___y_4641_: *mut LeanObject,
    mut v___y_4642_: *mut LeanObject,
    mut v___y_4643_: *mut LeanObject,
    mut v___y_4644_: *mut LeanObject,
    mut v___y_4645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    v___x_4647_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___redArg(v_upperBound_4628_, v___x_4629_, v_a_4630_, v_a_4633_, v_b_4634_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
    return v___x_4647_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_4648_: *mut LeanObject = *_args.add(0);
    let mut v___x_4649_: *mut LeanObject = *_args.add(1);
    let mut v_a_4650_: *mut LeanObject = *_args.add(2);
    let mut v_inst_4651_: *mut LeanObject = *_args.add(3);
    let mut v_R_4652_: *mut LeanObject = *_args.add(4);
    let mut v_a_4653_: *mut LeanObject = *_args.add(5);
    let mut v_b_4654_: *mut LeanObject = *_args.add(6);
    let mut v_c_4655_: *mut LeanObject = *_args.add(7);
    let mut v___y_4656_: *mut LeanObject = *_args.add(8);
    let mut v___y_4657_: *mut LeanObject = *_args.add(9);
    let mut v___y_4658_: *mut LeanObject = *_args.add(10);
    let mut v___y_4659_: *mut LeanObject = *_args.add(11);
    let mut v___y_4660_: *mut LeanObject = *_args.add(12);
    let mut v___y_4661_: *mut LeanObject = *_args.add(13);
    let mut v___y_4662_: *mut LeanObject = *_args.add(14);
    let mut v___y_4663_: *mut LeanObject = *_args.add(15);
    let mut v___y_4664_: *mut LeanObject = *_args.add(16);
    let mut v___y_4665_: *mut LeanObject = *_args.add(17);
    let mut v___y_4666_: *mut LeanObject = *_args.add(18);
    let mut v_res_4667_: *mut LeanObject = core::ptr::null_mut();
    v_res_4667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq_spec__1(v_upperBound_4648_, v___x_4649_, v_a_4650_, v_inst_4651_, v_R_4652_, v_a_4653_, v_b_4654_, v_c_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
    lean_dec(v___y_4665_);
    lean_dec_ref(v___y_4664_);
    lean_dec(v___y_4663_);
    lean_dec_ref(v___y_4662_);
    lean_dec(v___y_4661_);
    lean_dec_ref(v___y_4660_);
    lean_dec(v___y_4659_);
    lean_dec_ref(v___y_4658_);
    lean_dec(v___y_4657_);
    lean_dec(v___y_4656_);
    lean_dec_ref(v_a_4650_);
    lean_dec(v___x_4649_);
    lean_dec(v_upperBound_4648_);
    return v_res_4667_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: f64 = 0.0;
    v___x_4668_ = lean_unsigned_to_nat(0);
    v___x_4669_ = lean_float_of_nat(v___x_4668_);
    return v___x_4669_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(
    mut v_cls_4673_: *mut LeanObject,
    mut v_msg_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
    mut v___y_4677_: *mut LeanObject,
    mut v___y_4678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4685_: u8 = 0;
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4698_: u8 = 0;
    let mut v_tid_4699_: u64 = 0;
    let mut v_traces_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4703_: u8 = 0;
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: f64 = 0.0;
    let mut v___x_4706_: u8 = 0;
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4724_: u8 = 0;
    let mut v_isSharedCheck_4725_: u8 = 0;
    let mut v_isSharedCheck_4726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4680_ = lean_ctor_get(v___y_4677_, 5);
                v___x_4681_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents_spec__1_spec__1(v_msg_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
                v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
                v_isSharedCheck_4726_ = (!lean_is_exclusive(v___x_4681_)) as u8;
                if v_isSharedCheck_4726_ == 0 {
                    v___x_4684_ = v___x_4681_;
                    v_isShared_4685_ = v_isSharedCheck_4726_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4682_);
                    lean_dec(v___x_4681_);
                    v___x_4684_ = lean_box(0);
                    v_isShared_4685_ = v_isSharedCheck_4726_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4686_ = lean_st_ref_take(v___y_4678_);
                v_traceState_4687_ = lean_ctor_get(v___x_4686_, 4);
                v_env_4688_ = lean_ctor_get(v___x_4686_, 0);
                v_nextMacroScope_4689_ = lean_ctor_get(v___x_4686_, 1);
                v_ngen_4690_ = lean_ctor_get(v___x_4686_, 2);
                v_auxDeclNGen_4691_ = lean_ctor_get(v___x_4686_, 3);
                v_cache_4692_ = lean_ctor_get(v___x_4686_, 5);
                v_messages_4693_ = lean_ctor_get(v___x_4686_, 6);
                v_infoState_4694_ = lean_ctor_get(v___x_4686_, 7);
                v_snapshotTasks_4695_ = lean_ctor_get(v___x_4686_, 8);
                v_isSharedCheck_4725_ = (!lean_is_exclusive(v___x_4686_)) as u8;
                if v_isSharedCheck_4725_ == 0 {
                    v___x_4697_ = v___x_4686_;
                    v_isShared_4698_ = v_isSharedCheck_4725_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4695_);
                    lean_inc(v_infoState_4694_);
                    lean_inc(v_messages_4693_);
                    lean_inc(v_cache_4692_);
                    lean_inc(v_traceState_4687_);
                    lean_inc(v_auxDeclNGen_4691_);
                    lean_inc(v_ngen_4690_);
                    lean_inc(v_nextMacroScope_4689_);
                    lean_inc(v_env_4688_);
                    lean_dec(v___x_4686_);
                    v___x_4697_ = lean_box(0);
                    v_isShared_4698_ = v_isSharedCheck_4725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4699_ = lean_ctor_get_uint64(
                    v_traceState_4687_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4700_ = lean_ctor_get(v_traceState_4687_, 0);
                v_isSharedCheck_4724_ = (!lean_is_exclusive(v_traceState_4687_)) as u8;
                if v_isSharedCheck_4724_ == 0 {
                    v___x_4702_ = v_traceState_4687_;
                    v_isShared_4703_ = v_isSharedCheck_4724_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_4700_);
                    lean_dec(v_traceState_4687_);
                    v___x_4702_ = lean_box(0);
                    v_isShared_4703_ = v_isSharedCheck_4724_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4704_ = lean_box(0);
                v___x_4705_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__0);
                v___x_4706_ = 0;
                v___x_4707_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__1;
                v___x_4708_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4708_, 0, v_cls_4673_);
                lean_ctor_set(v___x_4708_, 1, v___x_4704_);
                lean_ctor_set(v___x_4708_, 2, v___x_4707_);
                lean_ctor_set_float(
                    v___x_4708_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4705_,
                );
                lean_ctor_set_float(
                    v___x_4708_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4705_,
                );
                lean_ctor_set_uint8(
                    v___x_4708_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4706_,
                );
                v___x_4709_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___closed__2;
                v___x_4710_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4710_, 0, v___x_4708_);
                lean_ctor_set(v___x_4710_, 1, v_a_4682_);
                lean_ctor_set(v___x_4710_, 2, v___x_4709_);
                lean_inc(v_ref_4680_);
                v___x_4711_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4711_, 0, v_ref_4680_);
                lean_ctor_set(v___x_4711_, 1, v___x_4710_);
                v___x_4712_ = l_Lean_PersistentArray_push___redArg(v_traces_4700_, v___x_4711_);
                if v_isShared_4703_ == 0 {
                    lean_ctor_set(v___x_4702_, 0, v___x_4712_);
                    v___x_4714_ = v___x_4702_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4723_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4723_, 0, v___x_4712_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4723_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4699_,
                    );
                    v___x_4714_ = v_reuseFailAlloc_4723_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4698_ == 0 {
                    lean_ctor_set(v___x_4697_, 4, v___x_4714_);
                    v___x_4716_ = v___x_4697_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4722_, 0, v_env_4688_);
                    lean_ctor_set(v_reuseFailAlloc_4722_, 1, v_nextMacroScope_4689_);
                    lean_ctor_set(v_reuseFailAlloc_4722_, 2, v_ngen_4690_);
                    lean_ctor_set(v_reuseFailAlloc_4722_, 3, v_auxDeclNGen_4691_);
                    lean_ctor_set(v_reuseFailAlloc_4722_, 4, v___x_4714_);
                    lean_ctor_set(v_reuseFailAlloc_4722_, 5, v_cache_4692_);
                    lean_ctor_set(v_reuseFailAlloc_4722_, 6, v_messages_4693_);
                    lean_ctor_set(v_reuseFailAlloc_4722_, 7, v_infoState_4694_);
                    lean_ctor_set(v_reuseFailAlloc_4722_, 8, v_snapshotTasks_4695_);
                    v___x_4716_ = v_reuseFailAlloc_4722_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4717_ = lean_st_ref_set(v___y_4678_, v___x_4716_);
                v___x_4718_ = lean_box(0);
                if v_isShared_4685_ == 0 {
                    lean_ctor_set(v___x_4684_, 0, v___x_4718_);
                    v___x_4720_ = v___x_4684_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4721_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4721_, 0, v___x_4718_);
                    v___x_4720_ = v_reuseFailAlloc_4721_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg___boxed(
    mut v_cls_4727_: *mut LeanObject,
    mut v_msg_4728_: *mut LeanObject,
    mut v___y_4729_: *mut LeanObject,
    mut v___y_4730_: *mut LeanObject,
    mut v___y_4731_: *mut LeanObject,
    mut v___y_4732_: *mut LeanObject,
    mut v___y_4733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4734_: *mut LeanObject = core::ptr::null_mut();
    v_res_4734_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_4727_, v_msg_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_);
    lean_dec(v___y_4732_);
    lean_dec_ref(v___y_4731_);
    lean_dec(v___y_4730_);
    lean_dec_ref(v___y_4729_);
    return v_res_4734_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    v___x_4745_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3;
    v___x_4746_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__5;
    v___x_4747_ = l_Lean_Name_append(v___x_4746_, v___x_4745_);
    return v___x_4747_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    v___x_4749_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__7;
    v___x_4750_ = l_Lean_stringToMessageData(v___x_4749_);
    return v___x_4750_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10()
-> *mut LeanObject {
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut LeanObject = core::ptr::null_mut();
    v___x_4752_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__9;
    v___x_4753_ = l_Lean_stringToMessageData(v___x_4752_);
    return v___x_4753_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(
    mut v_a_4754_: *mut LeanObject,
    mut v_as_x27_4755_: *mut LeanObject,
    mut v_b_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
    mut v___y_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
    mut v___y_4762_: *mut LeanObject,
    mut v___y_4763_: *mut LeanObject,
    mut v___y_4764_: *mut LeanObject,
    mut v___y_4765_: *mut LeanObject,
    mut v___y_4766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: u8 = 0;
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4777_: u8 = 0;
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: u8 = 0;
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4793_: u8 = 0;
    let mut v_inheritedTraceOptions_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: u8 = 0;
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4810_: u8 = 0;
    let mut v___x_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4814_: u8 = 0;
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: u8 = 0;
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4827_: u8 = 0;
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4755_) == 0 {
                    lean_dec_ref(v_a_4754_);
                    v___x_4768_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4768_, 0, v_b_4756_);
                    return v___x_4768_;
                } else {
                    v_head_4769_ = lean_ctor_get(v_as_x27_4755_, 0);
                    v_tail_4770_ = lean_ctor_get(v_as_x27_4755_, 1);
                    v___x_4771_ = lean_box(0);
                    v___x_4772_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_a_4754_,
                            v_head_4769_,
                        );
                    if v___x_4772_ == 0 {
                        lean_inc(v_head_4769_);
                        lean_inc_ref(v_a_4754_);
                        v___x_4773_ = l_Lean_Meta_Grind_mkEqHEqProof(
                            v_a_4754_,
                            v_head_4769_,
                            v___y_4757_,
                            v___y_4758_,
                            v___y_4759_,
                            v___y_4760_,
                            v___y_4761_,
                            v___y_4762_,
                            v___y_4763_,
                            v___y_4764_,
                            v___y_4765_,
                            v___y_4766_,
                        );
                        if lean_obj_tag(v___x_4773_) == 0 {
                            v_options_4774_ = lean_ctor_get(v___y_4765_, 2);
                            v_a_4775_ = lean_ctor_get(v___x_4773_, 0);
                            lean_inc(v_a_4775_);
                            lean_dec_ref_known(v___x_4773_, 1);
                            v_inheritedTraceOptions_4776_ = lean_ctor_get(v___y_4765_, 13);
                            v_hasTrace_4777_ = lean_ctor_get_uint8(
                                v_options_4774_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            );
                            v___x_4778_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__3;
                            if v_hasTrace_4777_ == 0 {
                                v___y_4780_ = v___y_4757_;
                                v___y_4781_ = v___y_4758_;
                                v___y_4782_ = v___y_4759_;
                                v___y_4783_ = v___y_4760_;
                                v___y_4784_ = v___y_4761_;
                                v___y_4785_ = v___y_4762_;
                                v___y_4786_ = v___y_4763_;
                                v___y_4787_ = v___y_4764_;
                                v___y_4788_ = v___y_4765_;
                                v___y_4789_ = v___y_4766_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4815_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6);
                                v___x_4816_ =
                                    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                        v_inheritedTraceOptions_4776_,
                                        v_options_4774_,
                                        v___x_4815_,
                                    );
                                if v___x_4816_ == 0 {
                                    v___y_4780_ = v___y_4757_;
                                    v___y_4781_ = v___y_4758_;
                                    v___y_4782_ = v___y_4759_;
                                    v___y_4783_ = v___y_4760_;
                                    v___y_4784_ = v___y_4761_;
                                    v___y_4785_ = v___y_4762_;
                                    v___y_4786_ = v___y_4763_;
                                    v___y_4787_ = v___y_4764_;
                                    v___y_4788_ = v___y_4765_;
                                    v___y_4789_ = v___y_4766_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_4817_ = l_Lean_Meta_Grind_updateLastTag(
                                        v___y_4757_,
                                        v___y_4758_,
                                        v___y_4759_,
                                        v___y_4760_,
                                        v___y_4761_,
                                        v___y_4762_,
                                        v___y_4763_,
                                        v___y_4764_,
                                        v___y_4765_,
                                        v___y_4766_,
                                    );
                                    if lean_obj_tag(v___x_4817_) == 0 {
                                        lean_dec_ref_known(v___x_4817_, 1);
                                        lean_inc_ref(v_a_4754_);
                                        v___x_4818_ = l_Lean_MessageData_ofExpr(v_a_4754_);
                                        v___x_4819_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__10);
                                        v___x_4820_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4820_, 0, v___x_4818_);
                                        lean_ctor_set(v___x_4820_, 1, v___x_4819_);
                                        lean_inc(v_head_4769_);
                                        v___x_4821_ = l_Lean_MessageData_ofExpr(v_head_4769_);
                                        v___x_4822_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4822_, 0, v___x_4820_);
                                        lean_ctor_set(v___x_4822_, 1, v___x_4821_);
                                        v___x_4823_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_4778_, v___x_4822_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_);
                                        if lean_obj_tag(v___x_4823_) == 0 {
                                            lean_dec_ref_known(v___x_4823_, 1);
                                            v___y_4780_ = v___y_4757_;
                                            v___y_4781_ = v___y_4758_;
                                            v___y_4782_ = v___y_4759_;
                                            v___y_4783_ = v___y_4760_;
                                            v___y_4784_ = v___y_4761_;
                                            v___y_4785_ = v___y_4762_;
                                            v___y_4786_ = v___y_4763_;
                                            v___y_4787_ = v___y_4764_;
                                            v___y_4788_ = v___y_4765_;
                                            v___y_4789_ = v___y_4766_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec(v_a_4775_);
                                            lean_dec_ref(v_a_4754_);
                                            return v___x_4823_;
                                        }
                                    } else {
                                        lean_dec(v_a_4775_);
                                        lean_dec_ref(v_a_4754_);
                                        return v___x_4817_;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v_a_4754_);
                            v_a_4824_ = lean_ctor_get(v___x_4773_, 0);
                            v_isSharedCheck_4831_ = (!lean_is_exclusive(v___x_4773_)) as u8;
                            if v_isSharedCheck_4831_ == 0 {
                                v___x_4826_ = v___x_4773_;
                                v_isShared_4827_ = v_isSharedCheck_4831_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4824_);
                                lean_dec(v___x_4773_);
                                v___x_4826_ = lean_box(0);
                                v_isShared_4827_ = v_isSharedCheck_4831_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_as_x27_4755_ = v_tail_4770_;
                        v_b_4756_ = v___x_4771_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4790_ = 0;
                lean_inc(v_a_4775_);
                v___x_4791_ = l_Lean_Meta_check(
                    v_a_4775_,
                    v___x_4790_,
                    v___y_4786_,
                    v___y_4787_,
                    v___y_4788_,
                    v___y_4789_,
                );
                if lean_obj_tag(v___x_4791_) == 0 {
                    lean_dec_ref_known(v___x_4791_, 1);
                    v_options_4792_ = lean_ctor_get(v___y_4788_, 2);
                    v_hasTrace_4793_ = lean_ctor_get_uint8(
                        v_options_4792_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4793_ == 0 {
                        lean_dec(v_a_4775_);
                        v_as_x27_4755_ = v_tail_4770_;
                        v_b_4756_ = v___x_4771_;
                        state = 0;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4795_ = lean_ctor_get(v___y_4788_, 13);
                        v___x_4796_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__6);
                        v___x_4797_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4795_,
                            v_options_4792_,
                            v___x_4796_,
                        );
                        if v___x_4797_ == 0 {
                            lean_dec(v_a_4775_);
                            v_as_x27_4755_ = v_tail_4770_;
                            v_b_4756_ = v___x_4771_;
                            state = 0;
                            continue;
                        } else {
                            v___x_4799_ = l_Lean_Meta_Grind_updateLastTag(
                                v___y_4780_,
                                v___y_4781_,
                                v___y_4782_,
                                v___y_4783_,
                                v___y_4784_,
                                v___y_4785_,
                                v___y_4786_,
                                v___y_4787_,
                                v___y_4788_,
                                v___y_4789_,
                            );
                            if lean_obj_tag(v___x_4799_) == 0 {
                                lean_dec_ref_known(v___x_4799_, 1);
                                lean_inc(v___y_4789_);
                                lean_inc_ref(v___y_4788_);
                                lean_inc(v___y_4787_);
                                lean_inc_ref(v___y_4786_);
                                v___x_4800_ = lean_infer_type(
                                    v_a_4775_,
                                    v___y_4786_,
                                    v___y_4787_,
                                    v___y_4788_,
                                    v___y_4789_,
                                );
                                if lean_obj_tag(v___x_4800_) == 0 {
                                    v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
                                    lean_inc(v_a_4801_);
                                    lean_dec_ref_known(v___x_4800_, 1);
                                    v___x_4802_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___closed__8);
                                    v___x_4803_ = l_Lean_MessageData_ofExpr(v_a_4801_);
                                    v___x_4804_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4804_, 0, v___x_4802_);
                                    lean_ctor_set(v___x_4804_, 1, v___x_4803_);
                                    v___x_4805_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v___x_4778_, v___x_4804_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_);
                                    if lean_obj_tag(v___x_4805_) == 0 {
                                        lean_dec_ref_known(v___x_4805_, 1);
                                        v_as_x27_4755_ = v_tail_4770_;
                                        v_b_4756_ = v___x_4771_;
                                        state = 0;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_a_4754_);
                                        return v___x_4805_;
                                    }
                                } else {
                                    lean_dec_ref(v_a_4754_);
                                    v_a_4807_ = lean_ctor_get(v___x_4800_, 0);
                                    v_isSharedCheck_4814_ = (!lean_is_exclusive(v___x_4800_)) as u8;
                                    if v_isSharedCheck_4814_ == 0 {
                                        v___x_4809_ = v___x_4800_;
                                        v_isShared_4810_ = v_isSharedCheck_4814_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4807_);
                                        lean_dec(v___x_4800_);
                                        v___x_4809_ = lean_box(0);
                                        v_isShared_4810_ = v_isSharedCheck_4814_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4775_);
                                lean_dec_ref(v_a_4754_);
                                return v___x_4799_;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_4775_);
                    lean_dec_ref(v_a_4754_);
                    return v___x_4791_;
                }
            }
            2 => {
                if v_isShared_4810_ == 0 {
                    v___x_4812_ = v___x_4809_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
                    v___x_4812_ = v_reuseFailAlloc_4813_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4812_;
            }
            4 => {
                if v_isShared_4827_ == 0 {
                    v___x_4829_ = v___x_4826_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
                    v___x_4829_ = v_reuseFailAlloc_4830_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg___boxed(
    mut v_a_4833_: *mut LeanObject,
    mut v_as_x27_4834_: *mut LeanObject,
    mut v_b_4835_: *mut LeanObject,
    mut v___y_4836_: *mut LeanObject,
    mut v___y_4837_: *mut LeanObject,
    mut v___y_4838_: *mut LeanObject,
    mut v___y_4839_: *mut LeanObject,
    mut v___y_4840_: *mut LeanObject,
    mut v___y_4841_: *mut LeanObject,
    mut v___y_4842_: *mut LeanObject,
    mut v___y_4843_: *mut LeanObject,
    mut v___y_4844_: *mut LeanObject,
    mut v___y_4845_: *mut LeanObject,
    mut v___y_4846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4847_: *mut LeanObject = core::ptr::null_mut();
    v_res_4847_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_4833_, v_as_x27_4834_, v_b_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
    lean_dec(v___y_4845_);
    lean_dec_ref(v___y_4844_);
    lean_dec(v___y_4843_);
    lean_dec_ref(v___y_4842_);
    lean_dec(v___y_4841_);
    lean_dec_ref(v___y_4840_);
    lean_dec(v___y_4839_);
    lean_dec_ref(v___y_4838_);
    lean_dec(v___y_4837_);
    lean_dec(v___y_4836_);
    lean_dec(v_as_x27_4834_);
    return v_res_4847_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(
    mut v_a_4848_: *mut LeanObject,
    mut v_as_x27_4849_: *mut LeanObject,
    mut v_b_4850_: *mut LeanObject,
    mut v___y_4851_: *mut LeanObject,
    mut v___y_4852_: *mut LeanObject,
    mut v___y_4853_: *mut LeanObject,
    mut v___y_4854_: *mut LeanObject,
    mut v___y_4855_: *mut LeanObject,
    mut v___y_4856_: *mut LeanObject,
    mut v___y_4857_: *mut LeanObject,
    mut v___y_4858_: *mut LeanObject,
    mut v___y_4859_: *mut LeanObject,
    mut v___y_4860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4849_) == 0 {
                    v___x_4862_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4862_, 0, v_b_4850_);
                    return v___x_4862_;
                } else {
                    v_head_4863_ = lean_ctor_get(v_as_x27_4849_, 0);
                    v_tail_4864_ = lean_ctor_get(v_as_x27_4849_, 1);
                    v___x_4865_ = lean_box(0);
                    lean_inc(v_head_4863_);
                    v___x_4866_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_head_4863_, v_a_4848_, v___x_4865_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
                    if lean_obj_tag(v___x_4866_) == 0 {
                        lean_dec_ref_known(v___x_4866_, 1);
                        v_as_x27_4849_ = v_tail_4864_;
                        v_b_4850_ = v___x_4865_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4866_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg___boxed(
    mut v_a_4868_: *mut LeanObject,
    mut v_as_x27_4869_: *mut LeanObject,
    mut v_b_4870_: *mut LeanObject,
    mut v___y_4871_: *mut LeanObject,
    mut v___y_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
    mut v___y_4875_: *mut LeanObject,
    mut v___y_4876_: *mut LeanObject,
    mut v___y_4877_: *mut LeanObject,
    mut v___y_4878_: *mut LeanObject,
    mut v___y_4879_: *mut LeanObject,
    mut v___y_4880_: *mut LeanObject,
    mut v___y_4881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4882_: *mut LeanObject = core::ptr::null_mut();
    v_res_4882_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_4868_, v_as_x27_4869_, v_b_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_);
    lean_dec(v___y_4880_);
    lean_dec_ref(v___y_4879_);
    lean_dec(v___y_4878_);
    lean_dec_ref(v___y_4877_);
    lean_dec(v___y_4876_);
    lean_dec_ref(v___y_4875_);
    lean_dec(v___y_4874_);
    lean_dec_ref(v___y_4873_);
    lean_dec(v___y_4872_);
    lean_dec(v___y_4871_);
    lean_dec(v_as_x27_4869_);
    lean_dec(v_a_4868_);
    return v_res_4882_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(
    mut v_as_x27_4883_: *mut LeanObject,
    mut v_b_4884_: *mut LeanObject,
    mut v___y_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
    mut v___y_4891_: *mut LeanObject,
    mut v___y_4892_: *mut LeanObject,
    mut v___y_4893_: *mut LeanObject,
    mut v___y_4894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4883_) == 0 {
                    v___x_4896_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4896_, 0, v_b_4884_);
                    return v___x_4896_;
                } else {
                    v_head_4897_ = lean_ctor_get(v_as_x27_4883_, 0);
                    v_tail_4898_ = lean_ctor_get(v_as_x27_4883_, 1);
                    v___x_4899_ = lean_box(0);
                    v___x_4900_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_head_4897_, v_head_4897_, v___x_4899_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_);
                    if lean_obj_tag(v___x_4900_) == 0 {
                        lean_dec_ref_known(v___x_4900_, 1);
                        v_as_x27_4883_ = v_tail_4898_;
                        v_b_4884_ = v___x_4899_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4900_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg___boxed(
    mut v_as_x27_4902_: *mut LeanObject,
    mut v_b_4903_: *mut LeanObject,
    mut v___y_4904_: *mut LeanObject,
    mut v___y_4905_: *mut LeanObject,
    mut v___y_4906_: *mut LeanObject,
    mut v___y_4907_: *mut LeanObject,
    mut v___y_4908_: *mut LeanObject,
    mut v___y_4909_: *mut LeanObject,
    mut v___y_4910_: *mut LeanObject,
    mut v___y_4911_: *mut LeanObject,
    mut v___y_4912_: *mut LeanObject,
    mut v___y_4913_: *mut LeanObject,
    mut v___y_4914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4915_: *mut LeanObject = core::ptr::null_mut();
    v_res_4915_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_4902_, v_b_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_);
    lean_dec(v___y_4913_);
    lean_dec_ref(v___y_4912_);
    lean_dec(v___y_4911_);
    lean_dec_ref(v___y_4910_);
    lean_dec(v___y_4909_);
    lean_dec_ref(v___y_4908_);
    lean_dec(v___y_4907_);
    lean_dec_ref(v___y_4906_);
    lean_dec(v___y_4905_);
    lean_dec(v___y_4904_);
    lean_dec(v_as_x27_4902_);
    return v_res_4915_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(
    mut v_a_4916_: *mut LeanObject,
    mut v_a_4917_: *mut LeanObject,
    mut v_a_4918_: *mut LeanObject,
    mut v_a_4919_: *mut LeanObject,
    mut v_a_4920_: *mut LeanObject,
    mut v_a_4921_: *mut LeanObject,
    mut v_a_4922_: *mut LeanObject,
    mut v_a_4923_: *mut LeanObject,
    mut v_a_4924_: *mut LeanObject,
    mut v_a_4925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: u8 = 0;
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_unused_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4927_ = lean_st_ref_get(v_a_4916_);
                v___x_4928_ = 0;
                v___x_4929_ = l_Lean_Meta_Grind_Goal_getEqcs(v___x_4927_, v___x_4928_);
                lean_dec(v___x_4927_);
                v___x_4930_ = lean_box(0);
                v___x_4931_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v___x_4929_, v___x_4930_, v_a_4916_, v_a_4917_, v_a_4918_, v_a_4919_, v_a_4920_, v_a_4921_, v_a_4922_, v_a_4923_, v_a_4924_, v_a_4925_);
                lean_dec(v___x_4929_);
                if lean_obj_tag(v___x_4931_) == 0 {
                    v_isSharedCheck_4938_ = (!lean_is_exclusive(v___x_4931_)) as u8;
                    if v_isSharedCheck_4938_ == 0 {
                        v_unused_4939_ = lean_ctor_get(v___x_4931_, 0);
                        lean_dec(v_unused_4939_);
                        v___x_4933_ = v___x_4931_;
                        v_isShared_4934_ = v_isSharedCheck_4938_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4931_);
                        v___x_4933_ = lean_box(0);
                        v_isShared_4934_ = v_isSharedCheck_4938_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4931_;
                }
            }
            1 => {
                if v_isShared_4934_ == 0 {
                    lean_ctor_set(v___x_4933_, 0, v___x_4930_);
                    v___x_4936_ = v___x_4933_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4930_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4936_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs___boxed(
    mut v_a_4940_: *mut LeanObject,
    mut v_a_4941_: *mut LeanObject,
    mut v_a_4942_: *mut LeanObject,
    mut v_a_4943_: *mut LeanObject,
    mut v_a_4944_: *mut LeanObject,
    mut v_a_4945_: *mut LeanObject,
    mut v_a_4946_: *mut LeanObject,
    mut v_a_4947_: *mut LeanObject,
    mut v_a_4948_: *mut LeanObject,
    mut v_a_4949_: *mut LeanObject,
    mut v_a_4950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4951_: *mut LeanObject = core::ptr::null_mut();
    v_res_4951_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(
        v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_,
        v_a_4948_, v_a_4949_,
    );
    lean_dec(v_a_4949_);
    lean_dec_ref(v_a_4948_);
    lean_dec(v_a_4947_);
    lean_dec_ref(v_a_4946_);
    lean_dec(v_a_4945_);
    lean_dec_ref(v_a_4944_);
    lean_dec(v_a_4943_);
    lean_dec_ref(v_a_4942_);
    lean_dec(v_a_4941_);
    lean_dec(v_a_4940_);
    return v_res_4951_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(
    mut v_cls_4952_: *mut LeanObject,
    mut v_msg_4953_: *mut LeanObject,
    mut v___y_4954_: *mut LeanObject,
    mut v___y_4955_: *mut LeanObject,
    mut v___y_4956_: *mut LeanObject,
    mut v___y_4957_: *mut LeanObject,
    mut v___y_4958_: *mut LeanObject,
    mut v___y_4959_: *mut LeanObject,
    mut v___y_4960_: *mut LeanObject,
    mut v___y_4961_: *mut LeanObject,
    mut v___y_4962_: *mut LeanObject,
    mut v___y_4963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    v___x_4965_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___redArg(v_cls_4952_, v_msg_4953_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
    return v___x_4965_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0___boxed(
    mut v_cls_4966_: *mut LeanObject,
    mut v_msg_4967_: *mut LeanObject,
    mut v___y_4968_: *mut LeanObject,
    mut v___y_4969_: *mut LeanObject,
    mut v___y_4970_: *mut LeanObject,
    mut v___y_4971_: *mut LeanObject,
    mut v___y_4972_: *mut LeanObject,
    mut v___y_4973_: *mut LeanObject,
    mut v___y_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
    mut v___y_4977_: *mut LeanObject,
    mut v___y_4978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4979_: *mut LeanObject = core::ptr::null_mut();
    v_res_4979_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__0(v_cls_4966_, v_msg_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
    lean_dec(v___y_4977_);
    lean_dec_ref(v___y_4976_);
    lean_dec(v___y_4975_);
    lean_dec_ref(v___y_4974_);
    lean_dec(v___y_4973_);
    lean_dec_ref(v___y_4972_);
    lean_dec(v___y_4971_);
    lean_dec_ref(v___y_4970_);
    lean_dec(v___y_4969_);
    lean_dec(v___y_4968_);
    return v_res_4979_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(
    mut v_a_4980_: *mut LeanObject,
    mut v_as_4981_: *mut LeanObject,
    mut v_as_x27_4982_: *mut LeanObject,
    mut v_b_4983_: *mut LeanObject,
    mut v_a_4984_: *mut LeanObject,
    mut v___y_4985_: *mut LeanObject,
    mut v___y_4986_: *mut LeanObject,
    mut v___y_4987_: *mut LeanObject,
    mut v___y_4988_: *mut LeanObject,
    mut v___y_4989_: *mut LeanObject,
    mut v___y_4990_: *mut LeanObject,
    mut v___y_4991_: *mut LeanObject,
    mut v___y_4992_: *mut LeanObject,
    mut v___y_4993_: *mut LeanObject,
    mut v___y_4994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    v___x_4996_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___redArg(v_a_4980_, v_as_x27_4982_, v_b_4983_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_);
    return v___x_4996_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1___boxed(
    mut v_a_4997_: *mut LeanObject,
    mut v_as_4998_: *mut LeanObject,
    mut v_as_x27_4999_: *mut LeanObject,
    mut v_b_5000_: *mut LeanObject,
    mut v_a_5001_: *mut LeanObject,
    mut v___y_5002_: *mut LeanObject,
    mut v___y_5003_: *mut LeanObject,
    mut v___y_5004_: *mut LeanObject,
    mut v___y_5005_: *mut LeanObject,
    mut v___y_5006_: *mut LeanObject,
    mut v___y_5007_: *mut LeanObject,
    mut v___y_5008_: *mut LeanObject,
    mut v___y_5009_: *mut LeanObject,
    mut v___y_5010_: *mut LeanObject,
    mut v___y_5011_: *mut LeanObject,
    mut v___y_5012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5013_: *mut LeanObject = core::ptr::null_mut();
    v_res_5013_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__1(v_a_4997_, v_as_4998_, v_as_x27_4999_, v_b_5000_, v_a_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
    lean_dec(v___y_5011_);
    lean_dec_ref(v___y_5010_);
    lean_dec(v___y_5009_);
    lean_dec_ref(v___y_5008_);
    lean_dec(v___y_5007_);
    lean_dec_ref(v___y_5006_);
    lean_dec(v___y_5005_);
    lean_dec_ref(v___y_5004_);
    lean_dec(v___y_5003_);
    lean_dec(v___y_5002_);
    lean_dec(v_as_x27_4999_);
    lean_dec(v_as_4998_);
    return v_res_5013_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(
    mut v_a_5014_: *mut LeanObject,
    mut v_as_5015_: *mut LeanObject,
    mut v_as_x27_5016_: *mut LeanObject,
    mut v_b_5017_: *mut LeanObject,
    mut v_a_5018_: *mut LeanObject,
    mut v___y_5019_: *mut LeanObject,
    mut v___y_5020_: *mut LeanObject,
    mut v___y_5021_: *mut LeanObject,
    mut v___y_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
    mut v___y_5026_: *mut LeanObject,
    mut v___y_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    v___x_5030_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___redArg(v_a_5014_, v_as_x27_5016_, v_b_5017_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_);
    return v___x_5030_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2___boxed(
    mut v_a_5031_: *mut LeanObject,
    mut v_as_5032_: *mut LeanObject,
    mut v_as_x27_5033_: *mut LeanObject,
    mut v_b_5034_: *mut LeanObject,
    mut v_a_5035_: *mut LeanObject,
    mut v___y_5036_: *mut LeanObject,
    mut v___y_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
    mut v___y_5042_: *mut LeanObject,
    mut v___y_5043_: *mut LeanObject,
    mut v___y_5044_: *mut LeanObject,
    mut v___y_5045_: *mut LeanObject,
    mut v___y_5046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5047_: *mut LeanObject = core::ptr::null_mut();
    v_res_5047_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__2(v_a_5031_, v_as_5032_, v_as_x27_5033_, v_b_5034_, v_a_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_);
    lean_dec(v___y_5045_);
    lean_dec_ref(v___y_5044_);
    lean_dec(v___y_5043_);
    lean_dec_ref(v___y_5042_);
    lean_dec(v___y_5041_);
    lean_dec_ref(v___y_5040_);
    lean_dec(v___y_5039_);
    lean_dec_ref(v___y_5038_);
    lean_dec(v___y_5037_);
    lean_dec(v___y_5036_);
    lean_dec(v_as_x27_5033_);
    lean_dec(v_as_5032_);
    lean_dec(v_a_5031_);
    return v_res_5047_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(
    mut v_as_5048_: *mut LeanObject,
    mut v_as_x27_5049_: *mut LeanObject,
    mut v_b_5050_: *mut LeanObject,
    mut v_a_5051_: *mut LeanObject,
    mut v___y_5052_: *mut LeanObject,
    mut v___y_5053_: *mut LeanObject,
    mut v___y_5054_: *mut LeanObject,
    mut v___y_5055_: *mut LeanObject,
    mut v___y_5056_: *mut LeanObject,
    mut v___y_5057_: *mut LeanObject,
    mut v___y_5058_: *mut LeanObject,
    mut v___y_5059_: *mut LeanObject,
    mut v___y_5060_: *mut LeanObject,
    mut v___y_5061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    v___x_5063_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___redArg(v_as_x27_5049_, v_b_5050_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
    return v___x_5063_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3___boxed(
    mut v_as_5064_: *mut LeanObject,
    mut v_as_x27_5065_: *mut LeanObject,
    mut v_b_5066_: *mut LeanObject,
    mut v_a_5067_: *mut LeanObject,
    mut v___y_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
    mut v___y_5071_: *mut LeanObject,
    mut v___y_5072_: *mut LeanObject,
    mut v___y_5073_: *mut LeanObject,
    mut v___y_5074_: *mut LeanObject,
    mut v___y_5075_: *mut LeanObject,
    mut v___y_5076_: *mut LeanObject,
    mut v___y_5077_: *mut LeanObject,
    mut v___y_5078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5079_: *mut LeanObject = core::ptr::null_mut();
    v_res_5079_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs_spec__3(v_as_5064_, v_as_x27_5065_, v_b_5066_, v_a_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_);
    lean_dec(v___y_5077_);
    lean_dec_ref(v___y_5076_);
    lean_dec(v___y_5075_);
    lean_dec_ref(v___y_5074_);
    lean_dec(v___y_5073_);
    lean_dec_ref(v___y_5072_);
    lean_dec(v___y_5071_);
    lean_dec_ref(v___y_5070_);
    lean_dec(v___y_5069_);
    lean_dec(v___y_5068_);
    lean_dec(v_as_x27_5065_);
    lean_dec(v_as_5064_);
    return v_res_5079_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(
    mut v_opts_5080_: *mut LeanObject,
    mut v_opt_5081_: *mut LeanObject,
) -> u8 {
    let mut v_name_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    v_name_5082_ = lean_ctor_get(v_opt_5081_, 0);
    v_defValue_5083_ = lean_ctor_get(v_opt_5081_, 1);
    v_map_5084_ = lean_ctor_get(v_opts_5080_, 0);
    v___x_5085_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5084_,
            v_name_5082_,
        );
    if lean_obj_tag(v___x_5085_) == 0 {
        let mut v___x_5086_: u8 = 0;
        v___x_5086_ = (lean_unbox(v_defValue_5083_) as u8);
        return v___x_5086_;
    } else {
        let mut v_val_5087_: *mut LeanObject = core::ptr::null_mut();
        v_val_5087_ = lean_ctor_get(v___x_5085_, 0);
        lean_inc(v_val_5087_);
        lean_dec_ref_known(v___x_5085_, 1);
        if lean_obj_tag(v_val_5087_) == 1 {
            let mut v_v_5088_: u8 = 0;
            v_v_5088_ = lean_ctor_get_uint8(v_val_5087_, 0 as u32);
            lean_dec_ref_known(v_val_5087_, 0);
            return v_v_5088_;
        } else {
            let mut v___x_5089_: u8 = 0;
            lean_dec(v_val_5087_);
            v___x_5089_ = (lean_unbox(v_defValue_5083_) as u8);
            return v___x_5089_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0___boxed(
    mut v_opts_5090_: *mut LeanObject,
    mut v_opt_5091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5092_: u8 = 0;
    let mut v_r_5093_: *mut LeanObject = core::ptr::null_mut();
    v_res_5092_ = l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(
        v_opts_5090_,
        v_opt_5091_,
    );
    lean_dec_ref(v_opt_5091_);
    lean_dec_ref(v_opts_5090_);
    v_r_5093_ = lean_box((v_res_5092_) as usize);
    return v_r_5093_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(
    mut v_as_5094_: *mut LeanObject,
    mut v_sz_5095_: usize,
    mut v_i_5096_: usize,
    mut v_b_5097_: *mut LeanObject,
    mut v___y_5098_: *mut LeanObject,
    mut v___y_5099_: *mut LeanObject,
    mut v___y_5100_: *mut LeanObject,
    mut v___y_5101_: *mut LeanObject,
    mut v___y_5102_: *mut LeanObject,
    mut v___y_5103_: *mut LeanObject,
    mut v___y_5104_: *mut LeanObject,
    mut v___y_5105_: *mut LeanObject,
    mut v___y_5106_: *mut LeanObject,
    mut v___y_5107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5109_: u8 = 0;
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_self_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: usize = 0;
    let mut v___x_5122_: usize = 0;
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: u8 = 0;
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5130_: u8 = 0;
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5134_: u8 = 0;
    let mut v_a_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5138_: u8 = 0;
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5142_: u8 = 0;
    let mut v_a_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5146_: u8 = 0;
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5109_ = lean_usize_dec_lt(v_i_5096_, v_sz_5095_);
                if v___x_5109_ == 0 {
                    v___x_5110_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5110_, 0, v_b_5097_);
                    return v___x_5110_;
                } else {
                    lean_dec_ref(v_b_5097_);
                    v___x_5111_ = lean_st_ref_get(v___y_5098_);
                    v_a_5112_ = lean_array_uget_borrowed(v_as_5094_, v_i_5096_);
                    lean_inc(v_a_5112_);
                    v___x_5113_ = l_Lean_Meta_Grind_Goal_getENode(
                        v___x_5111_,
                        v_a_5112_,
                        v___y_5104_,
                        v___y_5105_,
                        v___y_5106_,
                        v___y_5107_,
                    );
                    lean_dec(v___x_5111_);
                    if lean_obj_tag(v___x_5113_) == 0 {
                        v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
                        lean_inc(v_a_5114_);
                        lean_dec_ref_known(v___x_5113_, 1);
                        v_self_5115_ = lean_ctor_get(v_a_5114_, 0);
                        lean_inc_ref(v_self_5115_);
                        v___x_5116_ =
                            l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(
                                v_self_5115_,
                                v___y_5098_,
                                v___y_5099_,
                                v___y_5100_,
                                v___y_5101_,
                                v___y_5102_,
                                v___y_5103_,
                                v___y_5104_,
                                v___y_5105_,
                                v___y_5106_,
                                v___y_5107_,
                            );
                        if lean_obj_tag(v___x_5116_) == 0 {
                            lean_dec_ref_known(v___x_5116_, 1);
                            v___x_5117_ = lean_box(0);
                            v___x_5124_ = lean_box(0);
                            v___x_5125_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_5114_);
                            if v___x_5125_ == 0 {
                                lean_dec(v_a_5114_);
                                v_a_5119_ = v___x_5124_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5126_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_5114_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
                                if lean_obj_tag(v___x_5126_) == 0 {
                                    lean_dec_ref_known(v___x_5126_, 1);
                                    v_a_5119_ = v___x_5124_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
                                    v_isSharedCheck_5134_ = (!lean_is_exclusive(v___x_5126_)) as u8;
                                    if v_isSharedCheck_5134_ == 0 {
                                        v___x_5129_ = v___x_5126_;
                                        v_isShared_5130_ = v_isSharedCheck_5134_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5127_);
                                        lean_dec(v___x_5126_);
                                        v___x_5129_ = lean_box(0);
                                        v_isShared_5130_ = v_isSharedCheck_5134_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_5114_);
                            v_a_5135_ = lean_ctor_get(v___x_5116_, 0);
                            v_isSharedCheck_5142_ = (!lean_is_exclusive(v___x_5116_)) as u8;
                            if v_isSharedCheck_5142_ == 0 {
                                v___x_5137_ = v___x_5116_;
                                v_isShared_5138_ = v_isSharedCheck_5142_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_5135_);
                                lean_dec(v___x_5116_);
                                v___x_5137_ = lean_box(0);
                                v_isShared_5138_ = v_isSharedCheck_5142_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_5143_ = lean_ctor_get(v___x_5113_, 0);
                        v_isSharedCheck_5150_ = (!lean_is_exclusive(v___x_5113_)) as u8;
                        if v_isSharedCheck_5150_ == 0 {
                            v___x_5145_ = v___x_5113_;
                            v_isShared_5146_ = v_isSharedCheck_5150_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5143_);
                            lean_dec(v___x_5113_);
                            v___x_5145_ = lean_box(0);
                            v_isShared_5146_ = v_isSharedCheck_5150_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5120_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5120_, 0, v___x_5117_);
                lean_ctor_set(v___x_5120_, 1, v_a_5119_);
                v___x_5121_ = 1usize;
                v___x_5122_ = lean_usize_add(v_i_5096_, v___x_5121_);
                v_i_5096_ = v___x_5122_;
                v_b_5097_ = v___x_5120_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5130_ == 0 {
                    v___x_5132_ = v___x_5129_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5133_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_a_5127_);
                    v___x_5132_ = v_reuseFailAlloc_5133_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5132_;
            }
            4 => {
                if v_isShared_5138_ == 0 {
                    v___x_5140_ = v___x_5137_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5141_, 0, v_a_5135_);
                    v___x_5140_ = v_reuseFailAlloc_5141_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5140_;
            }
            6 => {
                if v_isShared_5146_ == 0 {
                    v___x_5148_ = v___x_5145_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5149_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5149_, 0, v_a_5143_);
                    v___x_5148_ = v_reuseFailAlloc_5149_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5___boxed(
    mut v_as_5151_: *mut LeanObject,
    mut v_sz_5152_: *mut LeanObject,
    mut v_i_5153_: *mut LeanObject,
    mut v_b_5154_: *mut LeanObject,
    mut v___y_5155_: *mut LeanObject,
    mut v___y_5156_: *mut LeanObject,
    mut v___y_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
    mut v___y_5159_: *mut LeanObject,
    mut v___y_5160_: *mut LeanObject,
    mut v___y_5161_: *mut LeanObject,
    mut v___y_5162_: *mut LeanObject,
    mut v___y_5163_: *mut LeanObject,
    mut v___y_5164_: *mut LeanObject,
    mut v___y_5165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5166_: usize = 0;
    let mut v_i_boxed_5167_: usize = 0;
    let mut v_res_5168_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5166_ = lean_unbox_usize(v_sz_5152_);
    lean_dec(v_sz_5152_);
    v_i_boxed_5167_ = lean_unbox_usize(v_i_5153_);
    lean_dec(v_i_5153_);
    v_res_5168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_5151_, v_sz_boxed_5166_, v_i_boxed_5167_, v_b_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_);
    lean_dec(v___y_5164_);
    lean_dec_ref(v___y_5163_);
    lean_dec(v___y_5162_);
    lean_dec_ref(v___y_5161_);
    lean_dec(v___y_5160_);
    lean_dec_ref(v___y_5159_);
    lean_dec(v___y_5158_);
    lean_dec_ref(v___y_5157_);
    lean_dec(v___y_5156_);
    lean_dec(v___y_5155_);
    lean_dec_ref(v_as_5151_);
    return v_res_5168_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(
    mut v_as_5172_: *mut LeanObject,
    mut v_sz_5173_: usize,
    mut v_i_5174_: usize,
    mut v_b_5175_: *mut LeanObject,
    mut v___y_5176_: *mut LeanObject,
    mut v___y_5177_: *mut LeanObject,
    mut v___y_5178_: *mut LeanObject,
    mut v___y_5179_: *mut LeanObject,
    mut v___y_5180_: *mut LeanObject,
    mut v___y_5181_: *mut LeanObject,
    mut v___y_5182_: *mut LeanObject,
    mut v___y_5183_: *mut LeanObject,
    mut v___y_5184_: *mut LeanObject,
    mut v___y_5185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5187_: u8 = 0;
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_self_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: usize = 0;
    let mut v___x_5198_: usize = 0;
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: u8 = 0;
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5205_: u8 = 0;
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5209_: u8 = 0;
    let mut v_a_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5213_: u8 = 0;
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5217_: u8 = 0;
    let mut v_a_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5221_: u8 = 0;
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5187_ = lean_usize_dec_lt(v_i_5174_, v_sz_5173_);
                if v___x_5187_ == 0 {
                    v___x_5188_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5188_, 0, v_b_5175_);
                    return v___x_5188_;
                } else {
                    lean_dec_ref(v_b_5175_);
                    v___x_5189_ = lean_st_ref_get(v___y_5176_);
                    v_a_5190_ = lean_array_uget_borrowed(v_as_5172_, v_i_5174_);
                    lean_inc(v_a_5190_);
                    v___x_5191_ = l_Lean_Meta_Grind_Goal_getENode(
                        v___x_5189_,
                        v_a_5190_,
                        v___y_5182_,
                        v___y_5183_,
                        v___y_5184_,
                        v___y_5185_,
                    );
                    lean_dec(v___x_5189_);
                    if lean_obj_tag(v___x_5191_) == 0 {
                        v_a_5192_ = lean_ctor_get(v___x_5191_, 0);
                        lean_inc(v_a_5192_);
                        lean_dec_ref_known(v___x_5191_, 1);
                        v_self_5193_ = lean_ctor_get(v_a_5192_, 0);
                        lean_inc_ref(v_self_5193_);
                        v___x_5194_ =
                            l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(
                                v_self_5193_,
                                v___y_5176_,
                                v___y_5177_,
                                v___y_5178_,
                                v___y_5179_,
                                v___y_5180_,
                                v___y_5181_,
                                v___y_5182_,
                                v___y_5183_,
                                v___y_5184_,
                                v___y_5185_,
                            );
                        if lean_obj_tag(v___x_5194_) == 0 {
                            lean_dec_ref_known(v___x_5194_, 1);
                            v___x_5200_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_5192_);
                            if v___x_5200_ == 0 {
                                lean_dec(v_a_5192_);
                                state = 1;
                                continue;
                            } else {
                                v___x_5201_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_5192_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
                                if lean_obj_tag(v___x_5201_) == 0 {
                                    lean_dec_ref_known(v___x_5201_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
                                    v_isSharedCheck_5209_ = (!lean_is_exclusive(v___x_5201_)) as u8;
                                    if v_isSharedCheck_5209_ == 0 {
                                        v___x_5204_ = v___x_5201_;
                                        v_isShared_5205_ = v_isSharedCheck_5209_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5202_);
                                        lean_dec(v___x_5201_);
                                        v___x_5204_ = lean_box(0);
                                        v_isShared_5205_ = v_isSharedCheck_5209_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_5192_);
                            v_a_5210_ = lean_ctor_get(v___x_5194_, 0);
                            v_isSharedCheck_5217_ = (!lean_is_exclusive(v___x_5194_)) as u8;
                            if v_isSharedCheck_5217_ == 0 {
                                v___x_5212_ = v___x_5194_;
                                v_isShared_5213_ = v_isSharedCheck_5217_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_5210_);
                                lean_dec(v___x_5194_);
                                v___x_5212_ = lean_box(0);
                                v_isShared_5213_ = v_isSharedCheck_5217_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_5218_ = lean_ctor_get(v___x_5191_, 0);
                        v_isSharedCheck_5225_ = (!lean_is_exclusive(v___x_5191_)) as u8;
                        if v_isSharedCheck_5225_ == 0 {
                            v___x_5220_ = v___x_5191_;
                            v_isShared_5221_ = v_isSharedCheck_5225_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5218_);
                            lean_dec(v___x_5191_);
                            v___x_5220_ = lean_box(0);
                            v_isShared_5221_ = v_isSharedCheck_5225_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___closed__0;
                v___x_5197_ = 1usize;
                v___x_5198_ = lean_usize_add(v_i_5174_, v___x_5197_);
                v___x_5199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2_spec__5(v_as_5172_, v_sz_5173_, v___x_5198_, v___x_5196_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_);
                return v___x_5199_;
            }
            2 => {
                if v_isShared_5205_ == 0 {
                    v___x_5207_ = v___x_5204_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
                    v___x_5207_ = v_reuseFailAlloc_5208_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5207_;
            }
            4 => {
                if v_isShared_5213_ == 0 {
                    v___x_5215_ = v___x_5212_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
                    v___x_5215_ = v_reuseFailAlloc_5216_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5215_;
            }
            6 => {
                if v_isShared_5221_ == 0 {
                    v___x_5223_ = v___x_5220_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
                    v___x_5223_ = v_reuseFailAlloc_5224_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2___boxed(
    mut v_as_5226_: *mut LeanObject,
    mut v_sz_5227_: *mut LeanObject,
    mut v_i_5228_: *mut LeanObject,
    mut v_b_5229_: *mut LeanObject,
    mut v___y_5230_: *mut LeanObject,
    mut v___y_5231_: *mut LeanObject,
    mut v___y_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
    mut v___y_5234_: *mut LeanObject,
    mut v___y_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
    mut v___y_5237_: *mut LeanObject,
    mut v___y_5238_: *mut LeanObject,
    mut v___y_5239_: *mut LeanObject,
    mut v___y_5240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5241_: usize = 0;
    let mut v_i_boxed_5242_: usize = 0;
    let mut v_res_5243_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5241_ = lean_unbox_usize(v_sz_5227_);
    lean_dec(v_sz_5227_);
    v_i_boxed_5242_ = lean_unbox_usize(v_i_5228_);
    lean_dec(v_i_5228_);
    v_res_5243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_as_5226_, v_sz_boxed_5241_, v_i_boxed_5242_, v_b_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
    lean_dec(v___y_5239_);
    lean_dec_ref(v___y_5238_);
    lean_dec(v___y_5237_);
    lean_dec_ref(v___y_5236_);
    lean_dec(v___y_5235_);
    lean_dec_ref(v___y_5234_);
    lean_dec(v___y_5233_);
    lean_dec_ref(v___y_5232_);
    lean_dec(v___y_5231_);
    lean_dec(v___y_5230_);
    lean_dec_ref(v_as_5226_);
    return v_res_5243_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(
    mut v_as_5244_: *mut LeanObject,
    mut v_sz_5245_: usize,
    mut v_i_5246_: usize,
    mut v_b_5247_: *mut LeanObject,
    mut v___y_5248_: *mut LeanObject,
    mut v___y_5249_: *mut LeanObject,
    mut v___y_5250_: *mut LeanObject,
    mut v___y_5251_: *mut LeanObject,
    mut v___y_5252_: *mut LeanObject,
    mut v___y_5253_: *mut LeanObject,
    mut v___y_5254_: *mut LeanObject,
    mut v___y_5255_: *mut LeanObject,
    mut v___y_5256_: *mut LeanObject,
    mut v___y_5257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5259_: u8 = 0;
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_self_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: usize = 0;
    let mut v___x_5272_: usize = 0;
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: u8 = 0;
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5280_: u8 = 0;
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5284_: u8 = 0;
    let mut v_a_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5288_: u8 = 0;
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5292_: u8 = 0;
    let mut v_a_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5296_: u8 = 0;
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5259_ = lean_usize_dec_lt(v_i_5246_, v_sz_5245_);
                if v___x_5259_ == 0 {
                    v___x_5260_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5260_, 0, v_b_5247_);
                    return v___x_5260_;
                } else {
                    lean_dec_ref(v_b_5247_);
                    v___x_5261_ = lean_st_ref_get(v___y_5248_);
                    v_a_5262_ = lean_array_uget_borrowed(v_as_5244_, v_i_5246_);
                    lean_inc(v_a_5262_);
                    v___x_5263_ = l_Lean_Meta_Grind_Goal_getENode(
                        v___x_5261_,
                        v_a_5262_,
                        v___y_5254_,
                        v___y_5255_,
                        v___y_5256_,
                        v___y_5257_,
                    );
                    lean_dec(v___x_5261_);
                    if lean_obj_tag(v___x_5263_) == 0 {
                        v_a_5264_ = lean_ctor_get(v___x_5263_, 0);
                        lean_inc(v_a_5264_);
                        lean_dec_ref_known(v___x_5263_, 1);
                        v_self_5265_ = lean_ctor_get(v_a_5264_, 0);
                        lean_inc_ref(v_self_5265_);
                        v___x_5266_ =
                            l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(
                                v_self_5265_,
                                v___y_5248_,
                                v___y_5249_,
                                v___y_5250_,
                                v___y_5251_,
                                v___y_5252_,
                                v___y_5253_,
                                v___y_5254_,
                                v___y_5255_,
                                v___y_5256_,
                                v___y_5257_,
                            );
                        if lean_obj_tag(v___x_5266_) == 0 {
                            lean_dec_ref_known(v___x_5266_, 1);
                            v___x_5267_ = lean_box(0);
                            v___x_5274_ = lean_box(0);
                            v___x_5275_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_5264_);
                            if v___x_5275_ == 0 {
                                lean_dec(v_a_5264_);
                                v_a_5269_ = v___x_5274_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5276_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_5264_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
                                if lean_obj_tag(v___x_5276_) == 0 {
                                    lean_dec_ref_known(v___x_5276_, 1);
                                    v_a_5269_ = v___x_5274_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
                                    v_isSharedCheck_5284_ = (!lean_is_exclusive(v___x_5276_)) as u8;
                                    if v_isSharedCheck_5284_ == 0 {
                                        v___x_5279_ = v___x_5276_;
                                        v_isShared_5280_ = v_isSharedCheck_5284_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5277_);
                                        lean_dec(v___x_5276_);
                                        v___x_5279_ = lean_box(0);
                                        v_isShared_5280_ = v_isSharedCheck_5284_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_5264_);
                            v_a_5285_ = lean_ctor_get(v___x_5266_, 0);
                            v_isSharedCheck_5292_ = (!lean_is_exclusive(v___x_5266_)) as u8;
                            if v_isSharedCheck_5292_ == 0 {
                                v___x_5287_ = v___x_5266_;
                                v_isShared_5288_ = v_isSharedCheck_5292_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_5285_);
                                lean_dec(v___x_5266_);
                                v___x_5287_ = lean_box(0);
                                v_isShared_5288_ = v_isSharedCheck_5292_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_5293_ = lean_ctor_get(v___x_5263_, 0);
                        v_isSharedCheck_5300_ = (!lean_is_exclusive(v___x_5263_)) as u8;
                        if v_isSharedCheck_5300_ == 0 {
                            v___x_5295_ = v___x_5263_;
                            v_isShared_5296_ = v_isSharedCheck_5300_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5293_);
                            lean_dec(v___x_5263_);
                            v___x_5295_ = lean_box(0);
                            v_isShared_5296_ = v_isSharedCheck_5300_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5270_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5270_, 0, v___x_5267_);
                lean_ctor_set(v___x_5270_, 1, v_a_5269_);
                v___x_5271_ = 1usize;
                v___x_5272_ = lean_usize_add(v_i_5246_, v___x_5271_);
                v_i_5246_ = v___x_5272_;
                v_b_5247_ = v___x_5270_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5280_ == 0 {
                    v___x_5282_ = v___x_5279_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_a_5277_);
                    v___x_5282_ = v_reuseFailAlloc_5283_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5282_;
            }
            4 => {
                if v_isShared_5288_ == 0 {
                    v___x_5290_ = v___x_5287_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
                    v___x_5290_ = v_reuseFailAlloc_5291_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5290_;
            }
            6 => {
                if v_isShared_5296_ == 0 {
                    v___x_5298_ = v___x_5295_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5299_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_a_5293_);
                    v___x_5298_ = v_reuseFailAlloc_5299_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4___boxed(
    mut v_as_5301_: *mut LeanObject,
    mut v_sz_5302_: *mut LeanObject,
    mut v_i_5303_: *mut LeanObject,
    mut v_b_5304_: *mut LeanObject,
    mut v___y_5305_: *mut LeanObject,
    mut v___y_5306_: *mut LeanObject,
    mut v___y_5307_: *mut LeanObject,
    mut v___y_5308_: *mut LeanObject,
    mut v___y_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
    mut v___y_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
    mut v___y_5315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5316_: usize = 0;
    let mut v_i_boxed_5317_: usize = 0;
    let mut v_res_5318_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5316_ = lean_unbox_usize(v_sz_5302_);
    lean_dec(v_sz_5302_);
    v_i_boxed_5317_ = lean_unbox_usize(v_i_5303_);
    lean_dec(v_i_5303_);
    v_res_5318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_5301_, v_sz_boxed_5316_, v_i_boxed_5317_, v_b_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_);
    lean_dec(v___y_5314_);
    lean_dec_ref(v___y_5313_);
    lean_dec(v___y_5312_);
    lean_dec_ref(v___y_5311_);
    lean_dec(v___y_5310_);
    lean_dec_ref(v___y_5309_);
    lean_dec(v___y_5308_);
    lean_dec_ref(v___y_5307_);
    lean_dec(v___y_5306_);
    lean_dec(v___y_5305_);
    lean_dec_ref(v_as_5301_);
    return v_res_5318_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(
    mut v_as_5322_: *mut LeanObject,
    mut v_sz_5323_: usize,
    mut v_i_5324_: usize,
    mut v_b_5325_: *mut LeanObject,
    mut v___y_5326_: *mut LeanObject,
    mut v___y_5327_: *mut LeanObject,
    mut v___y_5328_: *mut LeanObject,
    mut v___y_5329_: *mut LeanObject,
    mut v___y_5330_: *mut LeanObject,
    mut v___y_5331_: *mut LeanObject,
    mut v___y_5332_: *mut LeanObject,
    mut v___y_5333_: *mut LeanObject,
    mut v___y_5334_: *mut LeanObject,
    mut v___y_5335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5337_: u8 = 0;
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_self_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: usize = 0;
    let mut v___x_5348_: usize = 0;
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: u8 = 0;
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5355_: u8 = 0;
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5359_: u8 = 0;
    let mut v_a_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5363_: u8 = 0;
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5367_: u8 = 0;
    let mut v_a_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5371_: u8 = 0;
    let mut v___x_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5337_ = lean_usize_dec_lt(v_i_5324_, v_sz_5323_);
                if v___x_5337_ == 0 {
                    v___x_5338_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5338_, 0, v_b_5325_);
                    return v___x_5338_;
                } else {
                    lean_dec_ref(v_b_5325_);
                    v___x_5339_ = lean_st_ref_get(v___y_5326_);
                    v_a_5340_ = lean_array_uget_borrowed(v_as_5322_, v_i_5324_);
                    lean_inc(v_a_5340_);
                    v___x_5341_ = l_Lean_Meta_Grind_Goal_getENode(
                        v___x_5339_,
                        v_a_5340_,
                        v___y_5332_,
                        v___y_5333_,
                        v___y_5334_,
                        v___y_5335_,
                    );
                    lean_dec(v___x_5339_);
                    if lean_obj_tag(v___x_5341_) == 0 {
                        v_a_5342_ = lean_ctor_get(v___x_5341_, 0);
                        lean_inc(v_a_5342_);
                        lean_dec_ref_known(v___x_5341_, 1);
                        v_self_5343_ = lean_ctor_get(v_a_5342_, 0);
                        lean_inc_ref(v_self_5343_);
                        v___x_5344_ =
                            l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkParents(
                                v_self_5343_,
                                v___y_5326_,
                                v___y_5327_,
                                v___y_5328_,
                                v___y_5329_,
                                v___y_5330_,
                                v___y_5331_,
                                v___y_5332_,
                                v___y_5333_,
                                v___y_5334_,
                                v___y_5335_,
                            );
                        if lean_obj_tag(v___x_5344_) == 0 {
                            lean_dec_ref_known(v___x_5344_, 1);
                            v___x_5350_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_5342_);
                            if v___x_5350_ == 0 {
                                lean_dec(v_a_5342_);
                                state = 1;
                                continue;
                            } else {
                                v___x_5351_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkEqc(v_a_5342_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_);
                                if lean_obj_tag(v___x_5351_) == 0 {
                                    lean_dec_ref_known(v___x_5351_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    v_a_5352_ = lean_ctor_get(v___x_5351_, 0);
                                    v_isSharedCheck_5359_ = (!lean_is_exclusive(v___x_5351_)) as u8;
                                    if v_isSharedCheck_5359_ == 0 {
                                        v___x_5354_ = v___x_5351_;
                                        v_isShared_5355_ = v_isSharedCheck_5359_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5352_);
                                        lean_dec(v___x_5351_);
                                        v___x_5354_ = lean_box(0);
                                        v_isShared_5355_ = v_isSharedCheck_5359_;
                                        state = 2;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_5342_);
                            v_a_5360_ = lean_ctor_get(v___x_5344_, 0);
                            v_isSharedCheck_5367_ = (!lean_is_exclusive(v___x_5344_)) as u8;
                            if v_isSharedCheck_5367_ == 0 {
                                v___x_5362_ = v___x_5344_;
                                v_isShared_5363_ = v_isSharedCheck_5367_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_5360_);
                                lean_dec(v___x_5344_);
                                v___x_5362_ = lean_box(0);
                                v_isShared_5363_ = v_isSharedCheck_5367_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_5368_ = lean_ctor_get(v___x_5341_, 0);
                        v_isSharedCheck_5375_ = (!lean_is_exclusive(v___x_5341_)) as u8;
                        if v_isSharedCheck_5375_ == 0 {
                            v___x_5370_ = v___x_5341_;
                            v_isShared_5371_ = v_isSharedCheck_5375_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5368_);
                            lean_dec(v___x_5341_);
                            v___x_5370_ = lean_box(0);
                            v_isShared_5371_ = v_isSharedCheck_5375_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___closed__0;
                v___x_5347_ = 1usize;
                v___x_5348_ = lean_usize_add(v_i_5324_, v___x_5347_);
                v___x_5349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3_spec__4(v_as_5322_, v_sz_5323_, v___x_5348_, v___x_5346_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_);
                return v___x_5349_;
            }
            2 => {
                if v_isShared_5355_ == 0 {
                    v___x_5357_ = v___x_5354_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_a_5352_);
                    v___x_5357_ = v_reuseFailAlloc_5358_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5357_;
            }
            4 => {
                if v_isShared_5363_ == 0 {
                    v___x_5365_ = v___x_5362_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
                    v___x_5365_ = v_reuseFailAlloc_5366_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5365_;
            }
            6 => {
                if v_isShared_5371_ == 0 {
                    v___x_5373_ = v___x_5370_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
                    v___x_5373_ = v_reuseFailAlloc_5374_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3___boxed(
    mut v_as_5376_: *mut LeanObject,
    mut v_sz_5377_: *mut LeanObject,
    mut v_i_5378_: *mut LeanObject,
    mut v_b_5379_: *mut LeanObject,
    mut v___y_5380_: *mut LeanObject,
    mut v___y_5381_: *mut LeanObject,
    mut v___y_5382_: *mut LeanObject,
    mut v___y_5383_: *mut LeanObject,
    mut v___y_5384_: *mut LeanObject,
    mut v___y_5385_: *mut LeanObject,
    mut v___y_5386_: *mut LeanObject,
    mut v___y_5387_: *mut LeanObject,
    mut v___y_5388_: *mut LeanObject,
    mut v___y_5389_: *mut LeanObject,
    mut v___y_5390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5391_: usize = 0;
    let mut v_i_boxed_5392_: usize = 0;
    let mut v_res_5393_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5391_ = lean_unbox_usize(v_sz_5377_);
    lean_dec(v_sz_5377_);
    v_i_boxed_5392_ = lean_unbox_usize(v_i_5378_);
    lean_dec(v_i_5378_);
    v_res_5393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_as_5376_, v_sz_boxed_5391_, v_i_boxed_5392_, v_b_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
    lean_dec(v___y_5389_);
    lean_dec_ref(v___y_5388_);
    lean_dec(v___y_5387_);
    lean_dec_ref(v___y_5386_);
    lean_dec(v___y_5385_);
    lean_dec_ref(v___y_5384_);
    lean_dec(v___y_5383_);
    lean_dec_ref(v___y_5382_);
    lean_dec(v___y_5381_);
    lean_dec(v___y_5380_);
    lean_dec_ref(v_as_5376_);
    return v_res_5393_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(
    mut v_init_5394_: *mut LeanObject,
    mut v_n_5395_: *mut LeanObject,
    mut v_b_5396_: *mut LeanObject,
    mut v___y_5397_: *mut LeanObject,
    mut v___y_5398_: *mut LeanObject,
    mut v___y_5399_: *mut LeanObject,
    mut v___y_5400_: *mut LeanObject,
    mut v___y_5401_: *mut LeanObject,
    mut v___y_5402_: *mut LeanObject,
    mut v___y_5403_: *mut LeanObject,
    mut v___y_5404_: *mut LeanObject,
    mut v___y_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5411_: usize = 0;
    let mut v___x_5412_: usize = 0;
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5417_: u8 = 0;
    let mut v_fst_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut v_a_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut v_vs_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5440_: usize = 0;
    let mut v___x_5441_: usize = 0;
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5446_: u8 = 0;
    let mut v_fst_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5457_: u8 = 0;
    let mut v_a_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5461_: u8 = 0;
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5465_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_5395_) == 0 {
                    v_cs_5408_ = lean_ctor_get(v_n_5395_, 0);
                    v___x_5409_ = lean_box(0);
                    v___x_5410_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5410_, 0, v___x_5409_);
                    lean_ctor_set(v___x_5410_, 1, v_b_5396_);
                    v_sz_5411_ = lean_array_size(v_cs_5408_);
                    v___x_5412_ = 0usize;
                    v___x_5413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_5394_, v_cs_5408_, v_sz_5411_, v___x_5412_, v___x_5410_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
                    if lean_obj_tag(v___x_5413_) == 0 {
                        v_a_5414_ = lean_ctor_get(v___x_5413_, 0);
                        v_isSharedCheck_5428_ = (!lean_is_exclusive(v___x_5413_)) as u8;
                        if v_isSharedCheck_5428_ == 0 {
                            v___x_5416_ = v___x_5413_;
                            v_isShared_5417_ = v_isSharedCheck_5428_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5414_);
                            lean_dec(v___x_5413_);
                            v___x_5416_ = lean_box(0);
                            v_isShared_5417_ = v_isSharedCheck_5428_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5429_ = lean_ctor_get(v___x_5413_, 0);
                        v_isSharedCheck_5436_ = (!lean_is_exclusive(v___x_5413_)) as u8;
                        if v_isSharedCheck_5436_ == 0 {
                            v___x_5431_ = v___x_5413_;
                            v_isShared_5432_ = v_isSharedCheck_5436_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5429_);
                            lean_dec(v___x_5413_);
                            v___x_5431_ = lean_box(0);
                            v_isShared_5432_ = v_isSharedCheck_5436_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5437_ = lean_ctor_get(v_n_5395_, 0);
                    v___x_5438_ = lean_box(0);
                    v___x_5439_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5439_, 0, v___x_5438_);
                    lean_ctor_set(v___x_5439_, 1, v_b_5396_);
                    v_sz_5440_ = lean_array_size(v_vs_5437_);
                    v___x_5441_ = 0usize;
                    v___x_5442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__3(v_vs_5437_, v_sz_5440_, v___x_5441_, v___x_5439_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_);
                    if lean_obj_tag(v___x_5442_) == 0 {
                        v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
                        v_isSharedCheck_5457_ = (!lean_is_exclusive(v___x_5442_)) as u8;
                        if v_isSharedCheck_5457_ == 0 {
                            v___x_5445_ = v___x_5442_;
                            v_isShared_5446_ = v_isSharedCheck_5457_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5443_);
                            lean_dec(v___x_5442_);
                            v___x_5445_ = lean_box(0);
                            v_isShared_5446_ = v_isSharedCheck_5457_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5458_ = lean_ctor_get(v___x_5442_, 0);
                        v_isSharedCheck_5465_ = (!lean_is_exclusive(v___x_5442_)) as u8;
                        if v_isSharedCheck_5465_ == 0 {
                            v___x_5460_ = v___x_5442_;
                            v_isShared_5461_ = v_isSharedCheck_5465_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5458_);
                            lean_dec(v___x_5442_);
                            v___x_5460_ = lean_box(0);
                            v_isShared_5461_ = v_isSharedCheck_5465_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5418_ = lean_ctor_get(v_a_5414_, 0);
                if lean_obj_tag(v_fst_5418_) == 0 {
                    v_snd_5419_ = lean_ctor_get(v_a_5414_, 1);
                    lean_inc(v_snd_5419_);
                    lean_dec(v_a_5414_);
                    v___x_5420_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5420_, 0, v_snd_5419_);
                    if v_isShared_5417_ == 0 {
                        lean_ctor_set(v___x_5416_, 0, v___x_5420_);
                        v___x_5422_ = v___x_5416_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5420_);
                        v___x_5422_ = v_reuseFailAlloc_5423_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5418_);
                    lean_dec(v_a_5414_);
                    v_val_5424_ = lean_ctor_get(v_fst_5418_, 0);
                    lean_inc(v_val_5424_);
                    lean_dec_ref_known(v_fst_5418_, 1);
                    if v_isShared_5417_ == 0 {
                        lean_ctor_set(v___x_5416_, 0, v_val_5424_);
                        v___x_5426_ = v___x_5416_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_val_5424_);
                        v___x_5426_ = v_reuseFailAlloc_5427_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5422_;
            }
            3 => {
                return v___x_5426_;
            }
            4 => {
                if v_isShared_5432_ == 0 {
                    v___x_5434_ = v___x_5431_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
                    v___x_5434_ = v_reuseFailAlloc_5435_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5434_;
            }
            6 => {
                v_fst_5447_ = lean_ctor_get(v_a_5443_, 0);
                if lean_obj_tag(v_fst_5447_) == 0 {
                    v_snd_5448_ = lean_ctor_get(v_a_5443_, 1);
                    lean_inc(v_snd_5448_);
                    lean_dec(v_a_5443_);
                    v___x_5449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5449_, 0, v_snd_5448_);
                    if v_isShared_5446_ == 0 {
                        lean_ctor_set(v___x_5445_, 0, v___x_5449_);
                        v___x_5451_ = v___x_5445_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5452_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5452_, 0, v___x_5449_);
                        v___x_5451_ = v_reuseFailAlloc_5452_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5447_);
                    lean_dec(v_a_5443_);
                    v_val_5453_ = lean_ctor_get(v_fst_5447_, 0);
                    lean_inc(v_val_5453_);
                    lean_dec_ref_known(v_fst_5447_, 1);
                    if v_isShared_5446_ == 0 {
                        lean_ctor_set(v___x_5445_, 0, v_val_5453_);
                        v___x_5455_ = v___x_5445_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_val_5453_);
                        v___x_5455_ = v_reuseFailAlloc_5456_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5451_;
            }
            8 => {
                return v___x_5455_;
            }
            9 => {
                if v_isShared_5461_ == 0 {
                    v___x_5463_ = v___x_5460_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5464_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_a_5458_);
                    v___x_5463_ = v_reuseFailAlloc_5464_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(
    mut v_init_5466_: *mut LeanObject,
    mut v_as_5467_: *mut LeanObject,
    mut v_sz_5468_: usize,
    mut v_i_5469_: usize,
    mut v_b_5470_: *mut LeanObject,
    mut v___y_5471_: *mut LeanObject,
    mut v___y_5472_: *mut LeanObject,
    mut v___y_5473_: *mut LeanObject,
    mut v___y_5474_: *mut LeanObject,
    mut v___y_5475_: *mut LeanObject,
    mut v___y_5476_: *mut LeanObject,
    mut v___y_5477_: *mut LeanObject,
    mut v___y_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5482_: u8 = 0;
    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5487_: u8 = 0;
    let mut v_a_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5493_: u8 = 0;
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: usize = 0;
    let mut v___x_5506_: usize = 0;
    let mut v_reuseFailAlloc_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5509_: u8 = 0;
    let mut v_a_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5513_: u8 = 0;
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5517_: u8 = 0;
    let mut v_isSharedCheck_5518_: u8 = 0;
    let mut v_unused_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5482_ = lean_usize_dec_lt(v_i_5469_, v_sz_5468_);
                if v___x_5482_ == 0 {
                    v___x_5483_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5483_, 0, v_b_5470_);
                    return v___x_5483_;
                } else {
                    v_snd_5484_ = lean_ctor_get(v_b_5470_, 1);
                    v_isSharedCheck_5518_ = (!lean_is_exclusive(v_b_5470_)) as u8;
                    if v_isSharedCheck_5518_ == 0 {
                        v_unused_5519_ = lean_ctor_get(v_b_5470_, 0);
                        lean_dec(v_unused_5519_);
                        v___x_5486_ = v_b_5470_;
                        v_isShared_5487_ = v_isSharedCheck_5518_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5484_);
                        lean_dec(v_b_5470_);
                        v___x_5486_ = lean_box(0);
                        v_isShared_5487_ = v_isSharedCheck_5518_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5488_ = lean_array_uget_borrowed(v_as_5467_, v_i_5469_);
                lean_inc(v_snd_5484_);
                v___x_5489_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_5466_, v_a_5488_, v_snd_5484_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
                if lean_obj_tag(v___x_5489_) == 0 {
                    v_a_5490_ = lean_ctor_get(v___x_5489_, 0);
                    v_isSharedCheck_5509_ = (!lean_is_exclusive(v___x_5489_)) as u8;
                    if v_isSharedCheck_5509_ == 0 {
                        v___x_5492_ = v___x_5489_;
                        v_isShared_5493_ = v_isSharedCheck_5509_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5490_);
                        lean_dec(v___x_5489_);
                        v___x_5492_ = lean_box(0);
                        v_isShared_5493_ = v_isSharedCheck_5509_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5486_);
                    lean_dec(v_snd_5484_);
                    v_a_5510_ = lean_ctor_get(v___x_5489_, 0);
                    v_isSharedCheck_5517_ = (!lean_is_exclusive(v___x_5489_)) as u8;
                    if v_isSharedCheck_5517_ == 0 {
                        v___x_5512_ = v___x_5489_;
                        v_isShared_5513_ = v_isSharedCheck_5517_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5510_);
                        lean_dec(v___x_5489_);
                        v___x_5512_ = lean_box(0);
                        v_isShared_5513_ = v_isSharedCheck_5517_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_5490_) == 0 {
                    v___x_5494_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5494_, 0, v_a_5490_);
                    if v_isShared_5487_ == 0 {
                        lean_ctor_set(v___x_5486_, 0, v___x_5494_);
                        v___x_5496_ = v___x_5486_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5500_, 0, v___x_5494_);
                        lean_ctor_set(v_reuseFailAlloc_5500_, 1, v_snd_5484_);
                        v___x_5496_ = v_reuseFailAlloc_5500_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5492_);
                    lean_dec(v_snd_5484_);
                    v_a_5501_ = lean_ctor_get(v_a_5490_, 0);
                    lean_inc(v_a_5501_);
                    lean_dec_ref_known(v_a_5490_, 1);
                    v___x_5502_ = lean_box(0);
                    if v_isShared_5487_ == 0 {
                        lean_ctor_set(v___x_5486_, 1, v_a_5501_);
                        lean_ctor_set(v___x_5486_, 0, v___x_5502_);
                        v___x_5504_ = v___x_5486_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5508_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5508_, 0, v___x_5502_);
                        lean_ctor_set(v_reuseFailAlloc_5508_, 1, v_a_5501_);
                        v___x_5504_ = v_reuseFailAlloc_5508_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5493_ == 0 {
                    lean_ctor_set(v___x_5492_, 0, v___x_5496_);
                    v___x_5498_ = v___x_5492_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5499_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5499_, 0, v___x_5496_);
                    v___x_5498_ = v_reuseFailAlloc_5499_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5498_;
            }
            5 => {
                v___x_5505_ = 1usize;
                v___x_5506_ = lean_usize_add(v_i_5469_, v___x_5505_);
                v_i_5469_ = v___x_5506_;
                v_b_5470_ = v___x_5504_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5513_ == 0 {
                    v___x_5515_ = v___x_5512_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5510_);
                    v___x_5515_ = v_reuseFailAlloc_5516_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2___boxed(
    mut v_init_5520_: *mut LeanObject,
    mut v_as_5521_: *mut LeanObject,
    mut v_sz_5522_: *mut LeanObject,
    mut v_i_5523_: *mut LeanObject,
    mut v_b_5524_: *mut LeanObject,
    mut v___y_5525_: *mut LeanObject,
    mut v___y_5526_: *mut LeanObject,
    mut v___y_5527_: *mut LeanObject,
    mut v___y_5528_: *mut LeanObject,
    mut v___y_5529_: *mut LeanObject,
    mut v___y_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
    mut v___y_5533_: *mut LeanObject,
    mut v___y_5534_: *mut LeanObject,
    mut v___y_5535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5536_: usize = 0;
    let mut v_i_boxed_5537_: usize = 0;
    let mut v_res_5538_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5536_ = lean_unbox_usize(v_sz_5522_);
    lean_dec(v_sz_5522_);
    v_i_boxed_5537_ = lean_unbox_usize(v_i_5523_);
    lean_dec(v_i_5523_);
    v_res_5538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1_spec__2(v_init_5520_, v_as_5521_, v_sz_boxed_5536_, v_i_boxed_5537_, v_b_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_);
    lean_dec(v___y_5534_);
    lean_dec_ref(v___y_5533_);
    lean_dec(v___y_5532_);
    lean_dec_ref(v___y_5531_);
    lean_dec(v___y_5530_);
    lean_dec_ref(v___y_5529_);
    lean_dec(v___y_5528_);
    lean_dec_ref(v___y_5527_);
    lean_dec(v___y_5526_);
    lean_dec(v___y_5525_);
    lean_dec_ref(v_as_5521_);
    return v_res_5538_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1___boxed(
    mut v_init_5539_: *mut LeanObject,
    mut v_n_5540_: *mut LeanObject,
    mut v_b_5541_: *mut LeanObject,
    mut v___y_5542_: *mut LeanObject,
    mut v___y_5543_: *mut LeanObject,
    mut v___y_5544_: *mut LeanObject,
    mut v___y_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
    mut v___y_5548_: *mut LeanObject,
    mut v___y_5549_: *mut LeanObject,
    mut v___y_5550_: *mut LeanObject,
    mut v___y_5551_: *mut LeanObject,
    mut v___y_5552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5553_: *mut LeanObject = core::ptr::null_mut();
    v_res_5553_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_5539_, v_n_5540_, v_b_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_);
    lean_dec(v___y_5551_);
    lean_dec_ref(v___y_5550_);
    lean_dec(v___y_5549_);
    lean_dec_ref(v___y_5548_);
    lean_dec(v___y_5547_);
    lean_dec_ref(v___y_5546_);
    lean_dec(v___y_5545_);
    lean_dec_ref(v___y_5544_);
    lean_dec(v___y_5543_);
    lean_dec(v___y_5542_);
    lean_dec_ref(v_n_5540_);
    return v_res_5553_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(
    mut v_t_5554_: *mut LeanObject,
    mut v_init_5555_: *mut LeanObject,
    mut v___y_5556_: *mut LeanObject,
    mut v___y_5557_: *mut LeanObject,
    mut v___y_5558_: *mut LeanObject,
    mut v___y_5559_: *mut LeanObject,
    mut v___y_5560_: *mut LeanObject,
    mut v___y_5561_: *mut LeanObject,
    mut v___y_5562_: *mut LeanObject,
    mut v___y_5563_: *mut LeanObject,
    mut v___y_5564_: *mut LeanObject,
    mut v___y_5565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5573_: u8 = 0;
    let mut v_a_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5581_: usize = 0;
    let mut v___x_5582_: usize = 0;
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5587_: u8 = 0;
    let mut v_fst_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5597_: u8 = 0;
    let mut v_a_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5601_: u8 = 0;
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5605_: u8 = 0;
    let mut v_isSharedCheck_5606_: u8 = 0;
    let mut v_a_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5610_: u8 = 0;
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5567_ = lean_ctor_get(v_t_5554_, 0);
                v_tail_5568_ = lean_ctor_get(v_t_5554_, 1);
                v___x_5569_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__1(v_init_5555_, v_root_5567_, v_init_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
                if lean_obj_tag(v___x_5569_) == 0 {
                    v_a_5570_ = lean_ctor_get(v___x_5569_, 0);
                    v_isSharedCheck_5606_ = (!lean_is_exclusive(v___x_5569_)) as u8;
                    if v_isSharedCheck_5606_ == 0 {
                        v___x_5572_ = v___x_5569_;
                        v_isShared_5573_ = v_isSharedCheck_5606_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5570_);
                        lean_dec(v___x_5569_);
                        v___x_5572_ = lean_box(0);
                        v_isShared_5573_ = v_isSharedCheck_5606_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5607_ = lean_ctor_get(v___x_5569_, 0);
                    v_isSharedCheck_5614_ = (!lean_is_exclusive(v___x_5569_)) as u8;
                    if v_isSharedCheck_5614_ == 0 {
                        v___x_5609_ = v___x_5569_;
                        v_isShared_5610_ = v_isSharedCheck_5614_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5607_);
                        lean_dec(v___x_5569_);
                        v___x_5609_ = lean_box(0);
                        v_isShared_5610_ = v_isSharedCheck_5614_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_5570_) == 0 {
                    v_a_5574_ = lean_ctor_get(v_a_5570_, 0);
                    lean_inc(v_a_5574_);
                    lean_dec_ref_known(v_a_5570_, 1);
                    if v_isShared_5573_ == 0 {
                        lean_ctor_set(v___x_5572_, 0, v_a_5574_);
                        v___x_5576_ = v___x_5572_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5577_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_a_5574_);
                        v___x_5576_ = v_reuseFailAlloc_5577_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5572_);
                    v_a_5578_ = lean_ctor_get(v_a_5570_, 0);
                    lean_inc(v_a_5578_);
                    lean_dec_ref_known(v_a_5570_, 1);
                    v___x_5579_ = lean_box(0);
                    v___x_5580_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5580_, 0, v___x_5579_);
                    lean_ctor_set(v___x_5580_, 1, v_a_5578_);
                    v_sz_5581_ = lean_array_size(v_tail_5568_);
                    v___x_5582_ = 0usize;
                    v___x_5583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1_spec__2(v_tail_5568_, v_sz_5581_, v___x_5582_, v___x_5580_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
                    if lean_obj_tag(v___x_5583_) == 0 {
                        v_a_5584_ = lean_ctor_get(v___x_5583_, 0);
                        v_isSharedCheck_5597_ = (!lean_is_exclusive(v___x_5583_)) as u8;
                        if v_isSharedCheck_5597_ == 0 {
                            v___x_5586_ = v___x_5583_;
                            v_isShared_5587_ = v_isSharedCheck_5597_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5584_);
                            lean_dec(v___x_5583_);
                            v___x_5586_ = lean_box(0);
                            v_isShared_5587_ = v_isSharedCheck_5597_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5598_ = lean_ctor_get(v___x_5583_, 0);
                        v_isSharedCheck_5605_ = (!lean_is_exclusive(v___x_5583_)) as u8;
                        if v_isSharedCheck_5605_ == 0 {
                            v___x_5600_ = v___x_5583_;
                            v_isShared_5601_ = v_isSharedCheck_5605_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5598_);
                            lean_dec(v___x_5583_);
                            v___x_5600_ = lean_box(0);
                            v_isShared_5601_ = v_isSharedCheck_5605_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5576_;
            }
            3 => {
                v_fst_5588_ = lean_ctor_get(v_a_5584_, 0);
                if lean_obj_tag(v_fst_5588_) == 0 {
                    v_snd_5589_ = lean_ctor_get(v_a_5584_, 1);
                    lean_inc(v_snd_5589_);
                    lean_dec(v_a_5584_);
                    if v_isShared_5587_ == 0 {
                        lean_ctor_set(v___x_5586_, 0, v_snd_5589_);
                        v___x_5591_ = v___x_5586_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_snd_5589_);
                        v___x_5591_ = v_reuseFailAlloc_5592_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5588_);
                    lean_dec(v_a_5584_);
                    v_val_5593_ = lean_ctor_get(v_fst_5588_, 0);
                    lean_inc(v_val_5593_);
                    lean_dec_ref_known(v_fst_5588_, 1);
                    if v_isShared_5587_ == 0 {
                        lean_ctor_set(v___x_5586_, 0, v_val_5593_);
                        v___x_5595_ = v___x_5586_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5596_, 0, v_val_5593_);
                        v___x_5595_ = v_reuseFailAlloc_5596_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5591_;
            }
            5 => {
                return v___x_5595_;
            }
            6 => {
                if v_isShared_5601_ == 0 {
                    v___x_5603_ = v___x_5600_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_a_5598_);
                    v___x_5603_ = v_reuseFailAlloc_5604_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5603_;
            }
            8 => {
                if v_isShared_5610_ == 0 {
                    v___x_5612_ = v___x_5609_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5613_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 0, v_a_5607_);
                    v___x_5612_ = v_reuseFailAlloc_5613_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1___boxed(
    mut v_t_5615_: *mut LeanObject,
    mut v_init_5616_: *mut LeanObject,
    mut v___y_5617_: *mut LeanObject,
    mut v___y_5618_: *mut LeanObject,
    mut v___y_5619_: *mut LeanObject,
    mut v___y_5620_: *mut LeanObject,
    mut v___y_5621_: *mut LeanObject,
    mut v___y_5622_: *mut LeanObject,
    mut v___y_5623_: *mut LeanObject,
    mut v___y_5624_: *mut LeanObject,
    mut v___y_5625_: *mut LeanObject,
    mut v___y_5626_: *mut LeanObject,
    mut v___y_5627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5628_: *mut LeanObject = core::ptr::null_mut();
    v_res_5628_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(
        v_t_5615_,
        v_init_5616_,
        v___y_5617_,
        v___y_5618_,
        v___y_5619_,
        v___y_5620_,
        v___y_5621_,
        v___y_5622_,
        v___y_5623_,
        v___y_5624_,
        v___y_5625_,
        v___y_5626_,
    );
    lean_dec(v___y_5626_);
    lean_dec_ref(v___y_5625_);
    lean_dec(v___y_5624_);
    lean_dec_ref(v___y_5623_);
    lean_dec(v___y_5622_);
    lean_dec_ref(v___y_5621_);
    lean_dec(v___y_5620_);
    lean_dec_ref(v___y_5619_);
    lean_dec(v___y_5618_);
    lean_dec(v___y_5617_);
    lean_dec_ref(v_t_5615_);
    return v_res_5628_;
}
pub unsafe fn l_Lean_Meta_Grind_checkInvariants(
    mut v_expensive_5629_: u8,
    mut v_a_5630_: *mut LeanObject,
    mut v_a_5631_: *mut LeanObject,
    mut v_a_5632_: *mut LeanObject,
    mut v_a_5633_: *mut LeanObject,
    mut v_a_5634_: *mut LeanObject,
    mut v_a_5635_: *mut LeanObject,
    mut v_a_5636_: *mut LeanObject,
    mut v_a_5637_: *mut LeanObject,
    mut v_a_5638_: *mut LeanObject,
    mut v_a_5639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: u8 = 0;
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_5671_: u8 = 0;
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5680_: u8 = 0;
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5684_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_debug_5671_ = lean_ctor_get_uint8(
                    v_a_5632_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                );
                if v_debug_5671_ == 0 {
                    v___y_5645_ = v_a_5630_;
                    v___y_5646_ = v_a_5631_;
                    v___y_5647_ = v_a_5632_;
                    v___y_5648_ = v_a_5633_;
                    v___y_5649_ = v_a_5634_;
                    v___y_5650_ = v_a_5635_;
                    v___y_5651_ = v_a_5636_;
                    v___y_5652_ = v_a_5637_;
                    v___y_5653_ = v_a_5638_;
                    v___y_5654_ = v_a_5639_;
                    state = 2;
                    continue;
                } else {
                    v___x_5672_ = l_Lean_Meta_Grind_getExprs___redArg(v_a_5630_);
                    if lean_obj_tag(v___x_5672_) == 0 {
                        v_a_5673_ = lean_ctor_get(v___x_5672_, 0);
                        lean_inc(v_a_5673_);
                        lean_dec_ref_known(v___x_5672_, 1);
                        v___x_5674_ = lean_box(0);
                        v___x_5675_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_checkInvariants_spec__1(v_a_5673_, v___x_5674_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_);
                        lean_dec(v_a_5673_);
                        if lean_obj_tag(v___x_5675_) == 0 {
                            lean_dec_ref_known(v___x_5675_, 1);
                            if v_expensive_5629_ == 0 {
                                v___y_5660_ = v_a_5630_;
                                v___y_5661_ = v_a_5631_;
                                v___y_5662_ = v_a_5632_;
                                v___y_5663_ = v_a_5633_;
                                v___y_5664_ = v_a_5634_;
                                v___y_5665_ = v_a_5635_;
                                v___y_5666_ = v_a_5636_;
                                v___y_5667_ = v_a_5637_;
                                v___y_5668_ = v_a_5638_;
                                v___y_5669_ = v_a_5639_;
                                state = 3;
                                continue;
                            } else {
                                v___x_5676_ = l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkPtrEqImpliesStructEq(v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_, v_a_5637_, v_a_5638_, v_a_5639_);
                                if lean_obj_tag(v___x_5676_) == 0 {
                                    lean_dec_ref_known(v___x_5676_, 1);
                                    v___y_5660_ = v_a_5630_;
                                    v___y_5661_ = v_a_5631_;
                                    v___y_5662_ = v_a_5632_;
                                    v___y_5663_ = v_a_5633_;
                                    v___y_5664_ = v_a_5634_;
                                    v___y_5665_ = v_a_5635_;
                                    v___y_5666_ = v_a_5636_;
                                    v___y_5667_ = v_a_5637_;
                                    v___y_5668_ = v_a_5638_;
                                    v___y_5669_ = v_a_5639_;
                                    state = 3;
                                    continue;
                                } else {
                                    return v___x_5676_;
                                }
                            }
                        } else {
                            return v___x_5675_;
                        }
                    } else {
                        v_a_5677_ = lean_ctor_get(v___x_5672_, 0);
                        v_isSharedCheck_5684_ = (!lean_is_exclusive(v___x_5672_)) as u8;
                        if v_isSharedCheck_5684_ == 0 {
                            v___x_5679_ = v___x_5672_;
                            v_isShared_5680_ = v_isSharedCheck_5684_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5677_);
                            lean_dec(v___x_5672_);
                            v___x_5679_ = lean_box(0);
                            v_isShared_5680_ = v_isSharedCheck_5684_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5642_ = lean_box(0);
                v___x_5643_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5643_, 0, v___x_5642_);
                return v___x_5643_;
            }
            2 => {
                if v_expensive_5629_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v_options_5655_ = lean_ctor_get(v___y_5653_, 2);
                    v___x_5656_ = l_Lean_Meta_Grind_grind_debug_proofs;
                    v___x_5657_ =
                        l_Lean_Option_get___at___00Lean_Meta_Grind_checkInvariants_spec__0(
                            v_options_5655_,
                            v___x_5656_,
                        );
                    if v___x_5657_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_5658_ =
                            l___private_Lean_Meta_Tactic_Grind_Inv_0__Lean_Meta_Grind_checkProofs(
                                v___y_5645_,
                                v___y_5646_,
                                v___y_5647_,
                                v___y_5648_,
                                v___y_5649_,
                                v___y_5650_,
                                v___y_5651_,
                                v___y_5652_,
                                v___y_5653_,
                                v___y_5654_,
                            );
                        return v___x_5658_;
                    }
                }
            }
            3 => {
                v___x_5670_ = l_Lean_Meta_Grind_Solvers_checkInvariants(
                    v___y_5660_,
                    v___y_5661_,
                    v___y_5662_,
                    v___y_5663_,
                    v___y_5664_,
                    v___y_5665_,
                    v___y_5666_,
                    v___y_5667_,
                    v___y_5668_,
                    v___y_5669_,
                );
                if lean_obj_tag(v___x_5670_) == 0 {
                    lean_dec_ref_known(v___x_5670_, 1);
                    v___y_5645_ = v___y_5660_;
                    v___y_5646_ = v___y_5661_;
                    v___y_5647_ = v___y_5662_;
                    v___y_5648_ = v___y_5663_;
                    v___y_5649_ = v___y_5664_;
                    v___y_5650_ = v___y_5665_;
                    v___y_5651_ = v___y_5666_;
                    v___y_5652_ = v___y_5667_;
                    v___y_5653_ = v___y_5668_;
                    v___y_5654_ = v___y_5669_;
                    state = 2;
                    continue;
                } else {
                    return v___x_5670_;
                }
            }
            4 => {
                if v_isShared_5680_ == 0 {
                    v___x_5682_ = v___x_5679_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5683_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5683_, 0, v_a_5677_);
                    v___x_5682_ = v_reuseFailAlloc_5683_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5682_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_checkInvariants___boxed(
    mut v_expensive_5685_: *mut LeanObject,
    mut v_a_5686_: *mut LeanObject,
    mut v_a_5687_: *mut LeanObject,
    mut v_a_5688_: *mut LeanObject,
    mut v_a_5689_: *mut LeanObject,
    mut v_a_5690_: *mut LeanObject,
    mut v_a_5691_: *mut LeanObject,
    mut v_a_5692_: *mut LeanObject,
    mut v_a_5693_: *mut LeanObject,
    mut v_a_5694_: *mut LeanObject,
    mut v_a_5695_: *mut LeanObject,
    mut v_a_5696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expensive_boxed_5697_: u8 = 0;
    let mut v_res_5698_: *mut LeanObject = core::ptr::null_mut();
    v_expensive_boxed_5697_ = (lean_unbox(v_expensive_5685_) as u8);
    v_res_5698_ = l_Lean_Meta_Grind_checkInvariants(
        v_expensive_boxed_5697_,
        v_a_5686_,
        v_a_5687_,
        v_a_5688_,
        v_a_5689_,
        v_a_5690_,
        v_a_5691_,
        v_a_5692_,
        v_a_5693_,
        v_a_5694_,
        v_a_5695_,
    );
    lean_dec(v_a_5695_);
    lean_dec_ref(v_a_5694_);
    lean_dec(v_a_5693_);
    lean_dec_ref(v_a_5692_);
    lean_dec(v_a_5691_);
    lean_dec_ref(v_a_5690_);
    lean_dec(v_a_5689_);
    lean_dec_ref(v_a_5688_);
    lean_dec(v_a_5687_);
    lean_dec(v_a_5686_);
    return v_res_5698_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(
    mut v_x_5699_: *mut LeanObject,
    mut v___y_5700_: *mut LeanObject,
    mut v___y_5701_: *mut LeanObject,
    mut v___y_5702_: *mut LeanObject,
    mut v___y_5703_: *mut LeanObject,
    mut v___y_5704_: *mut LeanObject,
    mut v___y_5705_: *mut LeanObject,
    mut v___y_5706_: *mut LeanObject,
    mut v___y_5707_: *mut LeanObject,
    mut v___y_5708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5704_);
    lean_inc_ref(v___y_5703_);
    lean_inc(v___y_5702_);
    lean_inc_ref(v___y_5701_);
    lean_inc(v___y_5700_);
    v___x_5710_ = lean_apply_10(
        v_x_5699_,
        v___y_5700_,
        v___y_5701_,
        v___y_5702_,
        v___y_5703_,
        v___y_5704_,
        v___y_5705_,
        v___y_5706_,
        v___y_5707_,
        v___y_5708_,
        lean_box(0),
    );
    return v___x_5710_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed(
    mut v_x_5711_: *mut LeanObject,
    mut v___y_5712_: *mut LeanObject,
    mut v___y_5713_: *mut LeanObject,
    mut v___y_5714_: *mut LeanObject,
    mut v___y_5715_: *mut LeanObject,
    mut v___y_5716_: *mut LeanObject,
    mut v___y_5717_: *mut LeanObject,
    mut v___y_5718_: *mut LeanObject,
    mut v___y_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5722_: *mut LeanObject = core::ptr::null_mut();
    v_res_5722_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0(v_x_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_);
    lean_dec(v___y_5716_);
    lean_dec_ref(v___y_5715_);
    lean_dec(v___y_5714_);
    lean_dec_ref(v___y_5713_);
    lean_dec(v___y_5712_);
    return v_res_5722_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(
    mut v_mvarId_5723_: *mut LeanObject,
    mut v_x_5724_: *mut LeanObject,
    mut v___y_5725_: *mut LeanObject,
    mut v___y_5726_: *mut LeanObject,
    mut v___y_5727_: *mut LeanObject,
    mut v___y_5728_: *mut LeanObject,
    mut v___y_5729_: *mut LeanObject,
    mut v___y_5730_: *mut LeanObject,
    mut v___y_5731_: *mut LeanObject,
    mut v___y_5732_: *mut LeanObject,
    mut v___y_5733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5740_: u8 = 0;
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5744_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5729_);
                lean_inc_ref(v___y_5728_);
                lean_inc(v___y_5727_);
                lean_inc_ref(v___y_5726_);
                lean_inc(v___y_5725_);
                v___f_5735_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                lean_closure_set(v___f_5735_, 0, v_x_5724_);
                lean_closure_set(v___f_5735_, 1, v___y_5725_);
                lean_closure_set(v___f_5735_, 2, v___y_5726_);
                lean_closure_set(v___f_5735_, 3, v___y_5727_);
                lean_closure_set(v___f_5735_, 4, v___y_5728_);
                lean_closure_set(v___f_5735_, 5, v___y_5729_);
                v___x_5736_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_5723_,
                    v___f_5735_,
                    v___y_5730_,
                    v___y_5731_,
                    v___y_5732_,
                    v___y_5733_,
                );
                if lean_obj_tag(v___x_5736_) == 0 {
                    return v___x_5736_;
                } else {
                    v_a_5737_ = lean_ctor_get(v___x_5736_, 0);
                    v_isSharedCheck_5744_ = (!lean_is_exclusive(v___x_5736_)) as u8;
                    if v_isSharedCheck_5744_ == 0 {
                        v___x_5739_ = v___x_5736_;
                        v_isShared_5740_ = v_isSharedCheck_5744_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5737_);
                        lean_dec(v___x_5736_);
                        v___x_5739_ = lean_box(0);
                        v_isShared_5740_ = v_isSharedCheck_5744_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5740_ == 0 {
                    v___x_5742_ = v___x_5739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5743_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
                    v___x_5742_ = v_reuseFailAlloc_5743_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5742_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg___boxed(
    mut v_mvarId_5745_: *mut LeanObject,
    mut v_x_5746_: *mut LeanObject,
    mut v___y_5747_: *mut LeanObject,
    mut v___y_5748_: *mut LeanObject,
    mut v___y_5749_: *mut LeanObject,
    mut v___y_5750_: *mut LeanObject,
    mut v___y_5751_: *mut LeanObject,
    mut v___y_5752_: *mut LeanObject,
    mut v___y_5753_: *mut LeanObject,
    mut v___y_5754_: *mut LeanObject,
    mut v___y_5755_: *mut LeanObject,
    mut v___y_5756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5757_: *mut LeanObject = core::ptr::null_mut();
    v_res_5757_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(
            v_mvarId_5745_,
            v_x_5746_,
            v___y_5747_,
            v___y_5748_,
            v___y_5749_,
            v___y_5750_,
            v___y_5751_,
            v___y_5752_,
            v___y_5753_,
            v___y_5754_,
            v___y_5755_,
        );
    lean_dec(v___y_5755_);
    lean_dec_ref(v___y_5754_);
    lean_dec(v___y_5753_);
    lean_dec_ref(v___y_5752_);
    lean_dec(v___y_5751_);
    lean_dec_ref(v___y_5750_);
    lean_dec(v___y_5749_);
    lean_dec_ref(v___y_5748_);
    lean_dec(v___y_5747_);
    return v_res_5757_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(
    mut v_00_u03b1_5758_: *mut LeanObject,
    mut v_mvarId_5759_: *mut LeanObject,
    mut v_x_5760_: *mut LeanObject,
    mut v___y_5761_: *mut LeanObject,
    mut v___y_5762_: *mut LeanObject,
    mut v___y_5763_: *mut LeanObject,
    mut v___y_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
    mut v___y_5769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    v___x_5771_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(
            v_mvarId_5759_,
            v_x_5760_,
            v___y_5761_,
            v___y_5762_,
            v___y_5763_,
            v___y_5764_,
            v___y_5765_,
            v___y_5766_,
            v___y_5767_,
            v___y_5768_,
            v___y_5769_,
        );
    return v___x_5771_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___boxed(
    mut v_00_u03b1_5772_: *mut LeanObject,
    mut v_mvarId_5773_: *mut LeanObject,
    mut v_x_5774_: *mut LeanObject,
    mut v___y_5775_: *mut LeanObject,
    mut v___y_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
    mut v___y_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
    mut v___y_5781_: *mut LeanObject,
    mut v___y_5782_: *mut LeanObject,
    mut v___y_5783_: *mut LeanObject,
    mut v___y_5784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5785_: *mut LeanObject = core::ptr::null_mut();
    v_res_5785_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0(
        v_00_u03b1_5772_,
        v_mvarId_5773_,
        v_x_5774_,
        v___y_5775_,
        v___y_5776_,
        v___y_5777_,
        v___y_5778_,
        v___y_5779_,
        v___y_5780_,
        v___y_5781_,
        v___y_5782_,
        v___y_5783_,
    );
    lean_dec(v___y_5783_);
    lean_dec_ref(v___y_5782_);
    lean_dec(v___y_5781_);
    lean_dec_ref(v___y_5780_);
    lean_dec(v___y_5779_);
    lean_dec_ref(v___y_5778_);
    lean_dec(v___y_5777_);
    lean_dec_ref(v___y_5776_);
    lean_dec(v___y_5775_);
    return v_res_5785_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(
    mut v_goal_5786_: *mut LeanObject,
    mut v_expensive_5787_: u8,
    mut v___y_5788_: *mut LeanObject,
    mut v___y_5789_: *mut LeanObject,
    mut v___y_5790_: *mut LeanObject,
    mut v___y_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
    mut v___y_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
    mut v___y_5795_: *mut LeanObject,
    mut v___y_5796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5802_: u8 = 0;
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5808_: u8 = 0;
    let mut v_unused_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5813_: u8 = 0;
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5798_ = lean_st_mk_ref(v_goal_5786_);
                v___x_5799_ = l_Lean_Meta_Grind_checkInvariants(
                    v_expensive_5787_,
                    v___x_5798_,
                    v___y_5788_,
                    v___y_5789_,
                    v___y_5790_,
                    v___y_5791_,
                    v___y_5792_,
                    v___y_5793_,
                    v___y_5794_,
                    v___y_5795_,
                    v___y_5796_,
                );
                if lean_obj_tag(v___x_5799_) == 0 {
                    v_isSharedCheck_5808_ = (!lean_is_exclusive(v___x_5799_)) as u8;
                    if v_isSharedCheck_5808_ == 0 {
                        v_unused_5809_ = lean_ctor_get(v___x_5799_, 0);
                        lean_dec(v_unused_5809_);
                        v___x_5801_ = v___x_5799_;
                        v_isShared_5802_ = v_isSharedCheck_5808_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5799_);
                        v___x_5801_ = lean_box(0);
                        v_isShared_5802_ = v_isSharedCheck_5808_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5798_);
                    v_a_5810_ = lean_ctor_get(v___x_5799_, 0);
                    v_isSharedCheck_5817_ = (!lean_is_exclusive(v___x_5799_)) as u8;
                    if v_isSharedCheck_5817_ == 0 {
                        v___x_5812_ = v___x_5799_;
                        v_isShared_5813_ = v_isSharedCheck_5817_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5810_);
                        lean_dec(v___x_5799_);
                        v___x_5812_ = lean_box(0);
                        v_isShared_5813_ = v_isSharedCheck_5817_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5803_ = lean_st_ref_get(v___x_5798_);
                v___x_5804_ = lean_st_ref_get(v___x_5798_);
                lean_dec(v___x_5798_);
                lean_dec(v___x_5804_);
                if v_isShared_5802_ == 0 {
                    lean_ctor_set(v___x_5801_, 0, v___x_5803_);
                    v___x_5806_ = v___x_5801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5807_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5807_, 0, v___x_5803_);
                    v___x_5806_ = v_reuseFailAlloc_5807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5806_;
            }
            3 => {
                if v_isShared_5813_ == 0 {
                    v___x_5815_ = v___x_5812_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5816_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5816_, 0, v_a_5810_);
                    v___x_5815_ = v_reuseFailAlloc_5816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed(
    mut v_goal_5818_: *mut LeanObject,
    mut v_expensive_5819_: *mut LeanObject,
    mut v___y_5820_: *mut LeanObject,
    mut v___y_5821_: *mut LeanObject,
    mut v___y_5822_: *mut LeanObject,
    mut v___y_5823_: *mut LeanObject,
    mut v___y_5824_: *mut LeanObject,
    mut v___y_5825_: *mut LeanObject,
    mut v___y_5826_: *mut LeanObject,
    mut v___y_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expensive_boxed_5830_: u8 = 0;
    let mut v_res_5831_: *mut LeanObject = core::ptr::null_mut();
    v_expensive_boxed_5830_ = (lean_unbox(v_expensive_5819_) as u8);
    v_res_5831_ = l_Lean_Meta_Grind_Goal_checkInvariants___lam__0(
        v_goal_5818_,
        v_expensive_boxed_5830_,
        v___y_5820_,
        v___y_5821_,
        v___y_5822_,
        v___y_5823_,
        v___y_5824_,
        v___y_5825_,
        v___y_5826_,
        v___y_5827_,
        v___y_5828_,
    );
    lean_dec(v___y_5828_);
    lean_dec_ref(v___y_5827_);
    lean_dec(v___y_5826_);
    lean_dec_ref(v___y_5825_);
    lean_dec(v___y_5824_);
    lean_dec_ref(v___y_5823_);
    lean_dec(v___y_5822_);
    lean_dec_ref(v___y_5821_);
    lean_dec(v___y_5820_);
    return v_res_5831_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_checkInvariants(
    mut v_goal_5832_: *mut LeanObject,
    mut v_expensive_5833_: u8,
    mut v_a_5834_: *mut LeanObject,
    mut v_a_5835_: *mut LeanObject,
    mut v_a_5836_: *mut LeanObject,
    mut v_a_5837_: *mut LeanObject,
    mut v_a_5838_: *mut LeanObject,
    mut v_a_5839_: *mut LeanObject,
    mut v_a_5840_: *mut LeanObject,
    mut v_a_5841_: *mut LeanObject,
    mut v_a_5842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mvarId_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5850_: u8 = 0;
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5855_: u8 = 0;
    let mut v_unused_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5860_: u8 = 0;
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5864_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mvarId_5844_ = lean_ctor_get(v_goal_5832_, 1);
                lean_inc(v_mvarId_5844_);
                v___x_5845_ = lean_box((v_expensive_5833_) as usize);
                v___f_5846_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Goal_checkInvariants___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    2,
                );
                lean_closure_set(v___f_5846_, 0, v_goal_5832_);
                lean_closure_set(v___f_5846_, 1, v___x_5845_);
                v___x_5847_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_Goal_checkInvariants_spec__0___redArg(v_mvarId_5844_, v___f_5846_, v_a_5834_, v_a_5835_, v_a_5836_, v_a_5837_, v_a_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_);
                if lean_obj_tag(v___x_5847_) == 0 {
                    v_isSharedCheck_5855_ = (!lean_is_exclusive(v___x_5847_)) as u8;
                    if v_isSharedCheck_5855_ == 0 {
                        v_unused_5856_ = lean_ctor_get(v___x_5847_, 0);
                        lean_dec(v_unused_5856_);
                        v___x_5849_ = v___x_5847_;
                        v_isShared_5850_ = v_isSharedCheck_5855_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5847_);
                        v___x_5849_ = lean_box(0);
                        v_isShared_5850_ = v_isSharedCheck_5855_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5857_ = lean_ctor_get(v___x_5847_, 0);
                    v_isSharedCheck_5864_ = (!lean_is_exclusive(v___x_5847_)) as u8;
                    if v_isSharedCheck_5864_ == 0 {
                        v___x_5859_ = v___x_5847_;
                        v_isShared_5860_ = v_isSharedCheck_5864_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5857_);
                        lean_dec(v___x_5847_);
                        v___x_5859_ = lean_box(0);
                        v_isShared_5860_ = v_isSharedCheck_5864_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5851_ = lean_box(0);
                if v_isShared_5850_ == 0 {
                    lean_ctor_set(v___x_5849_, 0, v___x_5851_);
                    v___x_5853_ = v___x_5849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5854_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 0, v___x_5851_);
                    v___x_5853_ = v_reuseFailAlloc_5854_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5853_;
            }
            3 => {
                if v_isShared_5860_ == 0 {
                    v___x_5862_ = v___x_5859_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5863_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_a_5857_);
                    v___x_5862_ = v_reuseFailAlloc_5863_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5862_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_checkInvariants___boxed(
    mut v_goal_5865_: *mut LeanObject,
    mut v_expensive_5866_: *mut LeanObject,
    mut v_a_5867_: *mut LeanObject,
    mut v_a_5868_: *mut LeanObject,
    mut v_a_5869_: *mut LeanObject,
    mut v_a_5870_: *mut LeanObject,
    mut v_a_5871_: *mut LeanObject,
    mut v_a_5872_: *mut LeanObject,
    mut v_a_5873_: *mut LeanObject,
    mut v_a_5874_: *mut LeanObject,
    mut v_a_5875_: *mut LeanObject,
    mut v_a_5876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expensive_boxed_5877_: u8 = 0;
    let mut v_res_5878_: *mut LeanObject = core::ptr::null_mut();
    v_expensive_boxed_5877_ = (lean_unbox(v_expensive_5866_) as u8);
    v_res_5878_ = l_Lean_Meta_Grind_Goal_checkInvariants(
        v_goal_5865_,
        v_expensive_boxed_5877_,
        v_a_5867_,
        v_a_5868_,
        v_a_5869_,
        v_a_5870_,
        v_a_5871_,
        v_a_5872_,
        v_a_5873_,
        v_a_5874_,
        v_a_5875_,
    );
    lean_dec(v_a_5875_);
    lean_dec_ref(v_a_5874_);
    lean_dec(v_a_5873_);
    lean_dec_ref(v_a_5872_);
    lean_dec(v_a_5871_);
    lean_dec_ref(v_a_5870_);
    lean_dec(v_a_5869_);
    lean_dec_ref(v_a_5868_);
    lean_dec(v_a_5867_);
    return v_res_5878_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Inv(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Inv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Inv(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Init_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
}
