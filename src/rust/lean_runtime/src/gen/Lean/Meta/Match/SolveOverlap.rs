// Lean compiler output
// Module: Lean.Meta.Match.SolveOverlap
// Imports: Lean.Meta.Basic Lean.Meta.Tactic.Contradiction
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hash, l_Lean_Expr_isRawNatLit, l_Lean_FVarIdSet_insert, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkFVar, l_Lean_mkMVar,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_isImplementationDetail, l_Lean_LocalDecl_toExpr,
    l_Lean_LocalDecl_type, l_Lean_LocalDecl_userName,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkAbsurd;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_MVarId_getDecl, l_Lean_Meta_isExprDefEq, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::MatchUtil::{
    l_Lean_Meta_matchEq_x3f, l_Lean_Meta_matchHEq_x3f, l_Lean_Meta_matchNot_x3f,
};
use crate::r#gen::Lean::Meta::Tactic::Contradiction::{
    initialize_Lean_Meta_Tactic_Contradiction, l_Lean_MVarId_contradictionCore,
    runtime_initialize_Lean_Meta_Tactic_Contradiction,
};
use crate::r#gen::Lean::Meta::Tactic::Injection::l_Lean_Meta_injection;
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_MVarId_intros;
use crate::r#gen::Lean::Meta::Tactic::Subst::l_Lean_Meta_substVars;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::MetavarContext::l_Lean_instReprMetavarKind_repr;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [77, 97, 116, 99, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__2_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 69, 113, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__3_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__1_value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__2_value) as *mut LeanObject,17634115403684839930 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__3_value) as *mut LeanObject,4128573869278761614 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__5_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__6_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__8_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [105, 110, 106, 101, 99, 116, 105, 111, 110, 65, 110, 121, 70, 97, 105, 108, 101, 100, 32, 97, 116, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__8_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__10_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [44, 32, 101, 114, 114, 111, 114, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__10_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4_spec__7___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4_spec__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4_spec__7___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny___lam__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__0_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 111, 108, 118, 101, 32, 111, 118, 101, 114, 108, 97, 112, 32, 97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 44, 32, 117, 110, 115, 111, 108, 118, 101, 100, 32, 115, 117, 98, 103, 111, 97, 108, 0]};
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__2_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [112, 114, 111, 118, 101, 83, 117, 98, 103, 111, 97, 108, 76, 111, 111, 112, 10, 0]};
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_solveOverlap___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            115, 111, 108, 118, 101, 79, 118, 101, 114, 108, 97, 112, 32, 0,
        ],
    };
static mut l_Lean_Meta_Match_solveOverlap___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_solveOverlap___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_solveOverlap___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_solveOverlap___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_solveOverlap___closed__2_value: LeanStringObject<3> =
    LeanStringObject {
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
static mut l_Lean_Meta_Match_solveOverlap___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_solveOverlap___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_solveOverlap___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_solveOverlap___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Match_solveOverlap___closed__4_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Match_solveOverlap___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Match_solveOverlap___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Match_solveOverlap___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Match_solveOverlap___closed__5: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__4___redArg(
    mut v_mvarId_3035_: *mut LeanObject,
    mut v_x_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
    mut v___y_3039_: *mut LeanObject,
    mut v___y_3040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3046_: u8 = 0;
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3050_: u8 = 0;
    let mut v_a_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3054_: u8 = 0;
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3042_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_3035_,
                    v_x_3036_,
                    v___y_3037_,
                    v___y_3038_,
                    v___y_3039_,
                    v___y_3040_,
                );
                if lean_obj_tag(v___x_3042_) == 0 {
                    v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
                    v_isSharedCheck_3050_ = (!lean_is_exclusive(v___x_3042_)) as u8;
                    if v_isSharedCheck_3050_ == 0 {
                        v___x_3045_ = v___x_3042_;
                        v_isShared_3046_ = v_isSharedCheck_3050_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3043_);
                        lean_dec(v___x_3042_);
                        v___x_3045_ = lean_box(0);
                        v_isShared_3046_ = v_isSharedCheck_3050_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3051_ = lean_ctor_get(v___x_3042_, 0);
                    v_isSharedCheck_3058_ = (!lean_is_exclusive(v___x_3042_)) as u8;
                    if v_isSharedCheck_3058_ == 0 {
                        v___x_3053_ = v___x_3042_;
                        v_isShared_3054_ = v_isSharedCheck_3058_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3051_);
                        lean_dec(v___x_3042_);
                        v___x_3053_ = lean_box(0);
                        v_isShared_3054_ = v_isSharedCheck_3058_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3046_ == 0 {
                    v___x_3048_ = v___x_3045_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
                    v___x_3048_ = v_reuseFailAlloc_3049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3048_;
            }
            3 => {
                if v_isShared_3054_ == 0 {
                    v___x_3056_ = v___x_3053_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
                    v___x_3056_ = v_reuseFailAlloc_3057_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__4___redArg___boxed(
    mut v_mvarId_3059_: *mut LeanObject,
    mut v_x_3060_: *mut LeanObject,
    mut v___y_3061_: *mut LeanObject,
    mut v___y_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
    mut v___y_3064_: *mut LeanObject,
    mut v___y_3065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3066_: *mut LeanObject = core::ptr::null_mut();
    v_res_3066_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__4___redArg(v_mvarId_3059_, v_x_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
    lean_dec(v___y_3064_);
    lean_dec_ref(v___y_3063_);
    lean_dec(v___y_3062_);
    lean_dec_ref(v___y_3061_);
    return v_res_3066_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__4(
    mut v_00_u03b1_3067_: *mut LeanObject,
    mut v_mvarId_3068_: *mut LeanObject,
    mut v_x_3069_: *mut LeanObject,
    mut v___y_3070_: *mut LeanObject,
    mut v___y_3071_: *mut LeanObject,
    mut v___y_3072_: *mut LeanObject,
    mut v___y_3073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    v___x_3075_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__4___redArg(v_mvarId_3068_, v_x_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
    return v___x_3075_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__4___boxed(
    mut v_00_u03b1_3076_: *mut LeanObject,
    mut v_mvarId_3077_: *mut LeanObject,
    mut v_x_3078_: *mut LeanObject,
    mut v___y_3079_: *mut LeanObject,
    mut v___y_3080_: *mut LeanObject,
    mut v___y_3081_: *mut LeanObject,
    mut v___y_3082_: *mut LeanObject,
    mut v___y_3083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3084_: *mut LeanObject = core::ptr::null_mut();
    v_res_3084_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__4(v_00_u03b1_3076_, v_mvarId_3077_, v_x_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_);
    lean_dec(v___y_3082_);
    lean_dec_ref(v___y_3081_);
    lean_dec(v___y_3080_);
    lean_dec_ref(v___y_3079_);
    return v_res_3084_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0_spec__0___redArg(
    mut v_a_3085_: *mut LeanObject,
    mut v_x_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3086_) == 0 {
                    v___x_3087_ = lean_box(0);
                    return v___x_3087_;
                } else {
                    v_key_3088_ = lean_ctor_get(v_x_3086_, 0);
                    v_value_3089_ = lean_ctor_get(v_x_3086_, 1);
                    v_tail_3090_ = lean_ctor_get(v_x_3086_, 2);
                    v___x_3091_ = lean_expr_eqv(v_key_3088_, v_a_3085_);
                    if v___x_3091_ == 0 {
                        v_x_3086_ = v_tail_3090_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3089_);
                        v___x_3093_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3093_, 0, v_value_3089_);
                        return v___x_3093_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0_spec__0___redArg___boxed(
    mut v_a_3094_: *mut LeanObject,
    mut v_x_3095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3096_: *mut LeanObject = core::ptr::null_mut();
    v_res_3096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0_spec__0___redArg(v_a_3094_, v_x_3095_);
    lean_dec(v_x_3095_);
    lean_dec_ref(v_a_3094_);
    return v_res_3096_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(
    mut v_m_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u64 = 0;
    let mut v___x_3102_: u64 = 0;
    let mut v___x_3103_: u64 = 0;
    let mut v_fold_3104_: u64 = 0;
    let mut v___x_3105_: u64 = 0;
    let mut v___x_3106_: u64 = 0;
    let mut v___x_3107_: u64 = 0;
    let mut v___x_3108_: usize = 0;
    let mut v___x_3109_: usize = 0;
    let mut v___x_3110_: usize = 0;
    let mut v___x_3111_: usize = 0;
    let mut v___x_3112_: usize = 0;
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_3099_ = lean_ctor_get(v_m_3097_, 1);
    v___x_3100_ = lean_array_get_size(v_buckets_3099_);
    v___x_3101_ = l_Lean_Expr_hash(v_a_3098_);
    v___x_3102_ = 32u64;
    v___x_3103_ = lean_uint64_shift_right(v___x_3101_, v___x_3102_);
    v_fold_3104_ = lean_uint64_xor(v___x_3101_, v___x_3103_);
    v___x_3105_ = 16u64;
    v___x_3106_ = lean_uint64_shift_right(v_fold_3104_, v___x_3105_);
    v___x_3107_ = lean_uint64_xor(v_fold_3104_, v___x_3106_);
    v___x_3108_ = lean_uint64_to_usize(v___x_3107_);
    v___x_3109_ = lean_usize_of_nat(v___x_3100_);
    v___x_3110_ = 1usize;
    v___x_3111_ = lean_usize_sub(v___x_3109_, v___x_3110_);
    v___x_3112_ = lean_usize_land(v___x_3108_, v___x_3111_);
    v___x_3113_ = lean_array_uget_borrowed(v_buckets_3099_, v___x_3112_);
    v___x_3114_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0_spec__0___redArg(v_a_3098_, v___x_3113_);
    return v___x_3114_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg___boxed(
    mut v_m_3115_: *mut LeanObject,
    mut v_a_3116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3117_: *mut LeanObject = core::ptr::null_mut();
    v_res_3117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(v_m_3115_, v_a_3116_);
    lean_dec_ref(v_a_3116_);
    lean_dec_ref(v_m_3115_);
    return v_res_3117_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5_spec__8_spec__12___redArg(
    mut v_x_3118_: *mut LeanObject,
    mut v_x_3119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3125_: u8 = 0;
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: u64 = 0;
    let mut v___x_3128_: u64 = 0;
    let mut v___x_3129_: u64 = 0;
    let mut v_fold_3130_: u64 = 0;
    let mut v___x_3131_: u64 = 0;
    let mut v___x_3132_: u64 = 0;
    let mut v___x_3133_: u64 = 0;
    let mut v___x_3134_: usize = 0;
    let mut v___x_3135_: usize = 0;
    let mut v___x_3136_: usize = 0;
    let mut v___x_3137_: usize = 0;
    let mut v___x_3138_: usize = 0;
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3119_) == 0 {
                    return v_x_3118_;
                } else {
                    v_key_3120_ = lean_ctor_get(v_x_3119_, 0);
                    v_value_3121_ = lean_ctor_get(v_x_3119_, 1);
                    v_tail_3122_ = lean_ctor_get(v_x_3119_, 2);
                    v_isSharedCheck_3145_ = (!lean_is_exclusive(v_x_3119_)) as u8;
                    if v_isSharedCheck_3145_ == 0 {
                        v___x_3124_ = v_x_3119_;
                        v_isShared_3125_ = v_isSharedCheck_3145_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3122_);
                        lean_inc(v_value_3121_);
                        lean_inc(v_key_3120_);
                        lean_dec(v_x_3119_);
                        v___x_3124_ = lean_box(0);
                        v_isShared_3125_ = v_isSharedCheck_3145_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3126_ = lean_array_get_size(v_x_3118_);
                v___x_3127_ = l_Lean_Expr_hash(v_key_3120_);
                v___x_3128_ = 32u64;
                v___x_3129_ = lean_uint64_shift_right(v___x_3127_, v___x_3128_);
                v_fold_3130_ = lean_uint64_xor(v___x_3127_, v___x_3129_);
                v___x_3131_ = 16u64;
                v___x_3132_ = lean_uint64_shift_right(v_fold_3130_, v___x_3131_);
                v___x_3133_ = lean_uint64_xor(v_fold_3130_, v___x_3132_);
                v___x_3134_ = lean_uint64_to_usize(v___x_3133_);
                v___x_3135_ = lean_usize_of_nat(v___x_3126_);
                v___x_3136_ = 1usize;
                v___x_3137_ = lean_usize_sub(v___x_3135_, v___x_3136_);
                v___x_3138_ = lean_usize_land(v___x_3134_, v___x_3137_);
                v___x_3139_ = lean_array_uget_borrowed(v_x_3118_, v___x_3138_);
                lean_inc(v___x_3139_);
                if v_isShared_3125_ == 0 {
                    lean_ctor_set(v___x_3124_, 2, v___x_3139_);
                    v___x_3141_ = v___x_3124_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_key_3120_);
                    lean_ctor_set(v_reuseFailAlloc_3144_, 1, v_value_3121_);
                    lean_ctor_set(v_reuseFailAlloc_3144_, 2, v___x_3139_);
                    v___x_3141_ = v_reuseFailAlloc_3144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3142_ = lean_array_uset(v_x_3118_, v___x_3138_, v___x_3141_);
                v_x_3118_ = v___x_3142_;
                v_x_3119_ = v_tail_3122_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5_spec__8___redArg(
    mut v_i_3146_: *mut LeanObject,
    mut v_source_3147_: *mut LeanObject,
    mut v_target_3148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: u8 = 0;
    let mut v_es_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3149_ = lean_array_get_size(v_source_3147_);
                v___x_3150_ = lean_nat_dec_lt(v_i_3146_, v___x_3149_);
                if v___x_3150_ == 0 {
                    lean_dec_ref(v_source_3147_);
                    lean_dec(v_i_3146_);
                    return v_target_3148_;
                } else {
                    v_es_3151_ = lean_array_fget(v_source_3147_, v_i_3146_);
                    v___x_3152_ = lean_box(0);
                    v_source_3153_ = lean_array_fset(v_source_3147_, v_i_3146_, v___x_3152_);
                    v_target_3154_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5_spec__8_spec__12___redArg(v_target_3148_, v_es_3151_);
                    v___x_3155_ = lean_unsigned_to_nat(1);
                    v___x_3156_ = lean_nat_add(v_i_3146_, v___x_3155_);
                    lean_dec(v_i_3146_);
                    v_i_3146_ = v___x_3156_;
                    v_source_3147_ = v_source_3153_;
                    v_target_3148_ = v_target_3154_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5___redArg(
    mut v_data_3158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    v___x_3159_ = lean_array_get_size(v_data_3158_);
    v___x_3160_ = lean_unsigned_to_nat(2);
    v_nbuckets_3161_ = lean_nat_mul(v___x_3159_, v___x_3160_);
    v___x_3162_ = lean_unsigned_to_nat(0);
    v___x_3163_ = lean_box(0);
    v___x_3164_ = lean_mk_array(v_nbuckets_3161_, v___x_3163_);
    v___x_3165_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5_spec__8___redArg(v___x_3162_, v_data_3158_, v___x_3164_);
    return v___x_3165_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__4___redArg(
    mut v_a_3166_: *mut LeanObject,
    mut v_x_3167_: *mut LeanObject,
) -> u8 {
    let mut v___x_3168_: u8 = 0;
    let mut v_key_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3167_) == 0 {
                    v___x_3168_ = 0;
                    return v___x_3168_;
                } else {
                    v_key_3169_ = lean_ctor_get(v_x_3167_, 0);
                    v_tail_3170_ = lean_ctor_get(v_x_3167_, 2);
                    v___x_3171_ = lean_expr_eqv(v_key_3169_, v_a_3166_);
                    if v___x_3171_ == 0 {
                        v_x_3167_ = v_tail_3170_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3171_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__4___redArg___boxed(
    mut v_a_3173_: *mut LeanObject,
    mut v_x_3174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3175_: u8 = 0;
    let mut v_r_3176_: *mut LeanObject = core::ptr::null_mut();
    v_res_3175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__4___redArg(v_a_3173_, v_x_3174_);
    lean_dec(v_x_3174_);
    lean_dec_ref(v_a_3173_);
    v_r_3176_ = lean_box((v_res_3175_) as usize);
    return v_r_3176_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__6___redArg(
    mut v_a_3177_: *mut LeanObject,
    mut v_b_3178_: *mut LeanObject,
    mut v_x_3179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3185_: u8 = 0;
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3179_) == 0 {
                    lean_dec(v_b_3178_);
                    lean_dec_ref(v_a_3177_);
                    return v_x_3179_;
                } else {
                    v_key_3180_ = lean_ctor_get(v_x_3179_, 0);
                    v_value_3181_ = lean_ctor_get(v_x_3179_, 1);
                    v_tail_3182_ = lean_ctor_get(v_x_3179_, 2);
                    v_isSharedCheck_3194_ = (!lean_is_exclusive(v_x_3179_)) as u8;
                    if v_isSharedCheck_3194_ == 0 {
                        v___x_3184_ = v_x_3179_;
                        v_isShared_3185_ = v_isSharedCheck_3194_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3182_);
                        lean_inc(v_value_3181_);
                        lean_inc(v_key_3180_);
                        lean_dec(v_x_3179_);
                        v___x_3184_ = lean_box(0);
                        v_isShared_3185_ = v_isSharedCheck_3194_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3186_ = lean_expr_eqv(v_key_3180_, v_a_3177_);
                if v___x_3186_ == 0 {
                    v___x_3187_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__6___redArg(v_a_3177_, v_b_3178_, v_tail_3182_);
                    if v_isShared_3185_ == 0 {
                        lean_ctor_set(v___x_3184_, 2, v___x_3187_);
                        v___x_3189_ = v___x_3184_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_key_3180_);
                        lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_value_3181_);
                        lean_ctor_set(v_reuseFailAlloc_3190_, 2, v___x_3187_);
                        v___x_3189_ = v_reuseFailAlloc_3190_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3181_);
                    lean_dec(v_key_3180_);
                    if v_isShared_3185_ == 0 {
                        lean_ctor_set(v___x_3184_, 1, v_b_3178_);
                        lean_ctor_set(v___x_3184_, 0, v_a_3177_);
                        v___x_3192_ = v___x_3184_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3177_);
                        lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_b_3178_);
                        lean_ctor_set(v_reuseFailAlloc_3193_, 2, v_tail_3182_);
                        v___x_3192_ = v_reuseFailAlloc_3193_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3189_;
            }
            3 => {
                return v___x_3192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2___redArg(
    mut v_m_3195_: *mut LeanObject,
    mut v_a_3196_: *mut LeanObject,
    mut v_b_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3202_: u8 = 0;
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u64 = 0;
    let mut v___x_3205_: u64 = 0;
    let mut v___x_3206_: u64 = 0;
    let mut v_fold_3207_: u64 = 0;
    let mut v___x_3208_: u64 = 0;
    let mut v___x_3209_: u64 = 0;
    let mut v___x_3210_: u64 = 0;
    let mut v___x_3211_: usize = 0;
    let mut v___x_3212_: usize = 0;
    let mut v___x_3213_: usize = 0;
    let mut v___x_3214_: usize = 0;
    let mut v___x_3215_: usize = 0;
    let mut v_bkt_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: u8 = 0;
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v_val_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3198_ = lean_ctor_get(v_m_3195_, 0);
                v_buckets_3199_ = lean_ctor_get(v_m_3195_, 1);
                v_isSharedCheck_3242_ = (!lean_is_exclusive(v_m_3195_)) as u8;
                if v_isSharedCheck_3242_ == 0 {
                    v___x_3201_ = v_m_3195_;
                    v_isShared_3202_ = v_isSharedCheck_3242_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3199_);
                    lean_inc(v_size_3198_);
                    lean_dec(v_m_3195_);
                    v___x_3201_ = lean_box(0);
                    v_isShared_3202_ = v_isSharedCheck_3242_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3203_ = lean_array_get_size(v_buckets_3199_);
                v___x_3204_ = l_Lean_Expr_hash(v_a_3196_);
                v___x_3205_ = 32u64;
                v___x_3206_ = lean_uint64_shift_right(v___x_3204_, v___x_3205_);
                v_fold_3207_ = lean_uint64_xor(v___x_3204_, v___x_3206_);
                v___x_3208_ = 16u64;
                v___x_3209_ = lean_uint64_shift_right(v_fold_3207_, v___x_3208_);
                v___x_3210_ = lean_uint64_xor(v_fold_3207_, v___x_3209_);
                v___x_3211_ = lean_uint64_to_usize(v___x_3210_);
                v___x_3212_ = lean_usize_of_nat(v___x_3203_);
                v___x_3213_ = 1usize;
                v___x_3214_ = lean_usize_sub(v___x_3212_, v___x_3213_);
                v___x_3215_ = lean_usize_land(v___x_3211_, v___x_3214_);
                v_bkt_3216_ = lean_array_uget_borrowed(v_buckets_3199_, v___x_3215_);
                v___x_3217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__4___redArg(v_a_3196_, v_bkt_3216_);
                if v___x_3217_ == 0 {
                    v___x_3218_ = lean_unsigned_to_nat(1);
                    v_size_x27_3219_ = lean_nat_add(v_size_3198_, v___x_3218_);
                    lean_dec(v_size_3198_);
                    lean_inc(v_bkt_3216_);
                    v___x_3220_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3220_, 0, v_a_3196_);
                    lean_ctor_set(v___x_3220_, 1, v_b_3197_);
                    lean_ctor_set(v___x_3220_, 2, v_bkt_3216_);
                    v_buckets_x27_3221_ =
                        lean_array_uset(v_buckets_3199_, v___x_3215_, v___x_3220_);
                    v___x_3222_ = lean_unsigned_to_nat(4);
                    v___x_3223_ = lean_nat_mul(v_size_x27_3219_, v___x_3222_);
                    v___x_3224_ = lean_unsigned_to_nat(3);
                    v___x_3225_ = lean_nat_div(v___x_3223_, v___x_3224_);
                    lean_dec(v___x_3223_);
                    v___x_3226_ = lean_array_get_size(v_buckets_x27_3221_);
                    v___x_3227_ = lean_nat_dec_le(v___x_3225_, v___x_3226_);
                    lean_dec(v___x_3225_);
                    if v___x_3227_ == 0 {
                        v_val_3228_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5___redArg(v_buckets_x27_3221_);
                        if v_isShared_3202_ == 0 {
                            lean_ctor_set(v___x_3201_, 1, v_val_3228_);
                            lean_ctor_set(v___x_3201_, 0, v_size_x27_3219_);
                            v___x_3230_ = v___x_3201_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_size_x27_3219_);
                            lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_val_3228_);
                            v___x_3230_ = v_reuseFailAlloc_3231_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3202_ == 0 {
                            lean_ctor_set(v___x_3201_, 1, v_buckets_x27_3221_);
                            lean_ctor_set(v___x_3201_, 0, v_size_x27_3219_);
                            v___x_3233_ = v___x_3201_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_size_x27_3219_);
                            lean_ctor_set(v_reuseFailAlloc_3234_, 1, v_buckets_x27_3221_);
                            v___x_3233_ = v_reuseFailAlloc_3234_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3216_);
                    v___x_3235_ = lean_box(0);
                    v_buckets_x27_3236_ =
                        lean_array_uset(v_buckets_3199_, v___x_3215_, v___x_3235_);
                    v___x_3237_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__6___redArg(v_a_3196_, v_b_3197_, v_bkt_3216_);
                    v___x_3238_ = lean_array_uset(v_buckets_x27_3236_, v___x_3215_, v___x_3237_);
                    if v_isShared_3202_ == 0 {
                        lean_ctor_set(v___x_3201_, 1, v___x_3238_);
                        v___x_3240_ = v___x_3201_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_size_3198_);
                        lean_ctor_set(v_reuseFailAlloc_3241_, 1, v___x_3238_);
                        v___x_3240_ = v_reuseFailAlloc_3241_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3230_;
            }
            3 => {
                return v___x_3233_;
            }
            4 => {
                return v___x_3240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__7_spec__13___redArg(
    mut v_x_3243_: *mut LeanObject,
    mut v_x_3244_: *mut LeanObject,
    mut v_x_3245_: *mut LeanObject,
    mut v_x_3246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3251_: u8 = 0;
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: u8 = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: u8 = 0;
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3247_ = lean_ctor_get(v_x_3243_, 0);
                v_vs_3248_ = lean_ctor_get(v_x_3243_, 1);
                v_isSharedCheck_3272_ = (!lean_is_exclusive(v_x_3243_)) as u8;
                if v_isSharedCheck_3272_ == 0 {
                    v___x_3250_ = v_x_3243_;
                    v_isShared_3251_ = v_isSharedCheck_3272_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3248_);
                    lean_inc(v_ks_3247_);
                    lean_dec(v_x_3243_);
                    v___x_3250_ = lean_box(0);
                    v_isShared_3251_ = v_isSharedCheck_3272_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3252_ = lean_array_get_size(v_ks_3247_);
                v___x_3253_ = lean_nat_dec_lt(v_x_3244_, v___x_3252_);
                if v___x_3253_ == 0 {
                    lean_dec(v_x_3244_);
                    v___x_3254_ = lean_array_push(v_ks_3247_, v_x_3245_);
                    v___x_3255_ = lean_array_push(v_vs_3248_, v_x_3246_);
                    if v_isShared_3251_ == 0 {
                        lean_ctor_set(v___x_3250_, 1, v___x_3255_);
                        lean_ctor_set(v___x_3250_, 0, v___x_3254_);
                        v___x_3257_ = v___x_3250_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3254_);
                        lean_ctor_set(v_reuseFailAlloc_3258_, 1, v___x_3255_);
                        v___x_3257_ = v_reuseFailAlloc_3258_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3259_ = lean_array_fget_borrowed(v_ks_3247_, v_x_3244_);
                    v___x_3260_ = l_Lean_instBEqMVarId_beq(v_x_3245_, v_k_x27_3259_);
                    if v___x_3260_ == 0 {
                        if v_isShared_3251_ == 0 {
                            v___x_3262_ = v___x_3250_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_ks_3247_);
                            lean_ctor_set(v_reuseFailAlloc_3266_, 1, v_vs_3248_);
                            v___x_3262_ = v_reuseFailAlloc_3266_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3267_ = lean_array_fset(v_ks_3247_, v_x_3244_, v_x_3245_);
                        v___x_3268_ = lean_array_fset(v_vs_3248_, v_x_3244_, v_x_3246_);
                        lean_dec(v_x_3244_);
                        if v_isShared_3251_ == 0 {
                            lean_ctor_set(v___x_3250_, 1, v___x_3268_);
                            lean_ctor_set(v___x_3250_, 0, v___x_3267_);
                            v___x_3270_ = v___x_3250_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3267_);
                            lean_ctor_set(v_reuseFailAlloc_3271_, 1, v___x_3268_);
                            v___x_3270_ = v_reuseFailAlloc_3271_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3257_;
            }
            3 => {
                v___x_3263_ = lean_unsigned_to_nat(1);
                v___x_3264_ = lean_nat_add(v_x_3244_, v___x_3263_);
                lean_dec(v_x_3244_);
                v_x_3243_ = v___x_3262_;
                v_x_3244_ = v___x_3264_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__7___redArg(
    mut v_n_3273_: *mut LeanObject,
    mut v_k_3274_: *mut LeanObject,
    mut v_v_3275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    v___x_3276_ = lean_unsigned_to_nat(0);
    v___x_3277_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__7_spec__13___redArg(v_n_3273_, v___x_3276_, v_k_3274_, v_v_3275_);
    return v___x_3277_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_3278_: usize = 0;
    let mut v___x_3279_: usize = 0;
    let mut v___x_3280_: usize = 0;
    v___x_3278_ = 5usize;
    v___x_3279_ = 1usize;
    v___x_3280_ = lean_usize_shift_left(v___x_3279_, v___x_3278_);
    return v___x_3280_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_3281_: usize = 0;
    let mut v___x_3282_: usize = 0;
    let mut v___x_3283_: usize = 0;
    v___x_3281_ = 1usize;
    v___x_3282_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__0);
    v___x_3283_ = lean_usize_sub(v___x_3282_, v___x_3281_);
    return v___x_3283_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    v___x_3284_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3284_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg(
    mut v_x_3285_: *mut LeanObject,
    mut v_x_3286_: usize,
    mut v_x_3287_: usize,
    mut v_x_3288_: *mut LeanObject,
    mut v_x_3289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: usize = 0;
    let mut v___x_3292_: usize = 0;
    let mut v___x_3293_: usize = 0;
    let mut v___x_3294_: usize = 0;
    let mut v_j_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3300_: u8 = 0;
    let mut v_v_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3314_: u8 = 0;
    let mut v___x_3315_: u8 = 0;
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3321_: u8 = 0;
    let mut v_node_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3325_: u8 = 0;
    let mut v___x_3326_: usize = 0;
    let mut v___x_3327_: usize = 0;
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3334_: u8 = 0;
    let mut v_unused_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3340_: u8 = 0;
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3345_: u8 = 0;
    let mut v_ks_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: usize = 0;
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: u8 = 0;
    let mut v_reuseFailAlloc_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3285_) == 0 {
                    v_es_3290_ = lean_ctor_get(v_x_3285_, 0);
                    v___x_3291_ = 5usize;
                    v___x_3292_ = 1usize;
                    v___x_3293_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__1);
                    v___x_3294_ = lean_usize_land(v_x_3286_, v___x_3293_);
                    v_j_3295_ = lean_usize_to_nat(v___x_3294_);
                    v___x_3296_ = lean_array_get_size(v_es_3290_);
                    v___x_3297_ = lean_nat_dec_lt(v_j_3295_, v___x_3296_);
                    if v___x_3297_ == 0 {
                        lean_dec(v_j_3295_);
                        lean_dec(v_x_3289_);
                        lean_dec(v_x_3288_);
                        return v_x_3285_;
                    } else {
                        lean_inc_ref(v_es_3290_);
                        v_isSharedCheck_3334_ = (!lean_is_exclusive(v_x_3285_)) as u8;
                        if v_isSharedCheck_3334_ == 0 {
                            v_unused_3335_ = lean_ctor_get(v_x_3285_, 0);
                            lean_dec(v_unused_3335_);
                            v___x_3299_ = v_x_3285_;
                            v_isShared_3300_ = v_isSharedCheck_3334_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3285_);
                            v___x_3299_ = lean_box(0);
                            v_isShared_3300_ = v_isSharedCheck_3334_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3336_ = lean_ctor_get(v_x_3285_, 0);
                    v_vs_3337_ = lean_ctor_get(v_x_3285_, 1);
                    v_isSharedCheck_3357_ = (!lean_is_exclusive(v_x_3285_)) as u8;
                    if v_isSharedCheck_3357_ == 0 {
                        v___x_3339_ = v_x_3285_;
                        v_isShared_3340_ = v_isSharedCheck_3357_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3337_);
                        lean_inc(v_ks_3336_);
                        lean_dec(v_x_3285_);
                        v___x_3339_ = lean_box(0);
                        v_isShared_3340_ = v_isSharedCheck_3357_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3301_ = lean_array_fget(v_es_3290_, v_j_3295_);
                v___x_3302_ = lean_box(0);
                v_xs_x27_3303_ = lean_array_fset(v_es_3290_, v_j_3295_, v___x_3302_);
                match lean_obj_tag(v_v_3301_) {
                    0 => {
                        v_key_3310_ = lean_ctor_get(v_v_3301_, 0);
                        v_val_3311_ = lean_ctor_get(v_v_3301_, 1);
                        v_isSharedCheck_3321_ = (!lean_is_exclusive(v_v_3301_)) as u8;
                        if v_isSharedCheck_3321_ == 0 {
                            v___x_3313_ = v_v_3301_;
                            v_isShared_3314_ = v_isSharedCheck_3321_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3311_);
                            lean_inc(v_key_3310_);
                            lean_dec(v_v_3301_);
                            v___x_3313_ = lean_box(0);
                            v_isShared_3314_ = v_isSharedCheck_3321_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3322_ = lean_ctor_get(v_v_3301_, 0);
                        v_isSharedCheck_3332_ = (!lean_is_exclusive(v_v_3301_)) as u8;
                        if v_isSharedCheck_3332_ == 0 {
                            v___x_3324_ = v_v_3301_;
                            v_isShared_3325_ = v_isSharedCheck_3332_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3322_);
                            lean_dec(v_v_3301_);
                            v___x_3324_ = lean_box(0);
                            v_isShared_3325_ = v_isSharedCheck_3332_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3333_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3333_, 0, v_x_3288_);
                        lean_ctor_set(v___x_3333_, 1, v_x_3289_);
                        v___y_3305_ = v___x_3333_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3306_ = lean_array_fset(v_xs_x27_3303_, v_j_3295_, v___y_3305_);
                lean_dec(v_j_3295_);
                if v_isShared_3300_ == 0 {
                    lean_ctor_set(v___x_3299_, 0, v___x_3306_);
                    v___x_3308_ = v___x_3299_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
                    v___x_3308_ = v_reuseFailAlloc_3309_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3308_;
            }
            4 => {
                v___x_3315_ = l_Lean_instBEqMVarId_beq(v_x_3288_, v_key_3310_);
                if v___x_3315_ == 0 {
                    lean_del_object(v___x_3313_);
                    v___x_3316_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3310_,
                        v_val_3311_,
                        v_x_3288_,
                        v_x_3289_,
                    );
                    v___x_3317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3317_, 0, v___x_3316_);
                    v___y_3305_ = v___x_3317_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3311_);
                    lean_dec(v_key_3310_);
                    if v_isShared_3314_ == 0 {
                        lean_ctor_set(v___x_3313_, 1, v_x_3289_);
                        lean_ctor_set(v___x_3313_, 0, v_x_3288_);
                        v___x_3319_ = v___x_3313_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_x_3288_);
                        lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_x_3289_);
                        v___x_3319_ = v_reuseFailAlloc_3320_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3305_ = v___x_3319_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3326_ = lean_usize_shift_right(v_x_3286_, v___x_3291_);
                v___x_3327_ = lean_usize_add(v_x_3287_, v___x_3292_);
                v___x_3328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg(v_node_3322_, v___x_3326_, v___x_3327_, v_x_3288_, v_x_3289_);
                if v_isShared_3325_ == 0 {
                    lean_ctor_set(v___x_3324_, 0, v___x_3328_);
                    v___x_3330_ = v___x_3324_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3328_);
                    v___x_3330_ = v_reuseFailAlloc_3331_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3305_ = v___x_3330_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3340_ == 0 {
                    v___x_3342_ = v___x_3339_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_ks_3336_);
                    lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_vs_3337_);
                    v___x_3342_ = v_reuseFailAlloc_3356_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3343_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__7___redArg(v___x_3342_, v_x_3288_, v_x_3289_);
                v___x_3351_ = 7usize;
                v___x_3352_ = lean_usize_dec_le(v___x_3351_, v_x_3287_);
                if v___x_3352_ == 0 {
                    v___x_3353_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3343_);
                    v___x_3354_ = lean_unsigned_to_nat(4);
                    v___x_3355_ = lean_nat_dec_lt(v___x_3353_, v___x_3354_);
                    lean_dec(v___x_3353_);
                    v___y_3345_ = v___x_3355_;
                    state = 10;
                    continue;
                } else {
                    v___y_3345_ = v___x_3352_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3345_ == 0 {
                    v_ks_3346_ = lean_ctor_get(v_newNode_3343_, 0);
                    lean_inc_ref(v_ks_3346_);
                    v_vs_3347_ = lean_ctor_get(v_newNode_3343_, 1);
                    lean_inc_ref(v_vs_3347_);
                    lean_dec_ref(v_newNode_3343_);
                    v___x_3348_ = lean_unsigned_to_nat(0);
                    v___x_3349_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___closed__2);
                    v___x_3350_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__8___redArg(v_x_3287_, v_ks_3346_, v_vs_3347_, v___x_3348_, v___x_3349_);
                    lean_dec_ref(v_vs_3347_);
                    lean_dec_ref(v_ks_3346_);
                    return v___x_3350_;
                } else {
                    return v_newNode_3343_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__8___redArg(
    mut v_depth_3358_: usize,
    mut v_keys_3359_: *mut LeanObject,
    mut v_vals_3360_: *mut LeanObject,
    mut v_i_3361_: *mut LeanObject,
    mut v_entries_3362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: u8 = 0;
    let mut v_k_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: u64 = 0;
    let mut v_h_3368_: usize = 0;
    let mut v___x_3369_: usize = 0;
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: usize = 0;
    let mut v___x_3372_: usize = 0;
    let mut v___x_3373_: usize = 0;
    let mut v_h_3374_: usize = 0;
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3363_ = lean_array_get_size(v_keys_3359_);
                v___x_3364_ = lean_nat_dec_lt(v_i_3361_, v___x_3363_);
                if v___x_3364_ == 0 {
                    lean_dec(v_i_3361_);
                    return v_entries_3362_;
                } else {
                    v_k_3365_ = lean_array_fget_borrowed(v_keys_3359_, v_i_3361_);
                    v_v_3366_ = lean_array_fget_borrowed(v_vals_3360_, v_i_3361_);
                    v___x_3367_ = l_Lean_instHashableMVarId_hash(v_k_3365_);
                    v_h_3368_ = lean_uint64_to_usize(v___x_3367_);
                    v___x_3369_ = 5usize;
                    v___x_3370_ = lean_unsigned_to_nat(1);
                    v___x_3371_ = 1usize;
                    v___x_3372_ = lean_usize_sub(v_depth_3358_, v___x_3371_);
                    v___x_3373_ = lean_usize_mul(v___x_3369_, v___x_3372_);
                    v_h_3374_ = lean_usize_shift_right(v_h_3368_, v___x_3373_);
                    v___x_3375_ = lean_nat_add(v_i_3361_, v___x_3370_);
                    lean_dec(v_i_3361_);
                    lean_inc(v_v_3366_);
                    lean_inc(v_k_3365_);
                    v___x_3376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg(v_entries_3362_, v_h_3374_, v_depth_3358_, v_k_3365_, v_v_3366_);
                    v_i_3361_ = v___x_3375_;
                    v_entries_3362_ = v___x_3376_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_depth_3378_: *mut LeanObject,
    mut v_keys_3379_: *mut LeanObject,
    mut v_vals_3380_: *mut LeanObject,
    mut v_i_3381_: *mut LeanObject,
    mut v_entries_3382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3383_: usize = 0;
    let mut v_res_3384_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3383_ = lean_unbox_usize(v_depth_3378_);
    lean_dec(v_depth_3378_);
    v_res_3384_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__8___redArg(v_depth_boxed_3383_, v_keys_3379_, v_vals_3380_, v_i_3381_, v_entries_3382_);
    lean_dec_ref(v_vals_3380_);
    lean_dec_ref(v_keys_3379_);
    return v_res_3384_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_x_3385_: *mut LeanObject,
    mut v_x_3386_: *mut LeanObject,
    mut v_x_3387_: *mut LeanObject,
    mut v_x_3388_: *mut LeanObject,
    mut v_x_3389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_8821__boxed_3390_: usize = 0;
    let mut v_x_8822__boxed_3391_: usize = 0;
    let mut v_res_3392_: *mut LeanObject = core::ptr::null_mut();
    v_x_8821__boxed_3390_ = lean_unbox_usize(v_x_3386_);
    lean_dec(v_x_3386_);
    v_x_8822__boxed_3391_ = lean_unbox_usize(v_x_3387_);
    lean_dec(v_x_3387_);
    v_res_3392_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg(v_x_3385_, v_x_8821__boxed_3390_, v_x_8822__boxed_3391_, v_x_3388_, v_x_3389_);
    return v_res_3392_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2___redArg(
    mut v_x_3393_: *mut LeanObject,
    mut v_x_3394_: *mut LeanObject,
    mut v_x_3395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3396_: u64 = 0;
    let mut v___x_3397_: usize = 0;
    let mut v___x_3398_: usize = 0;
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v___x_3396_ = l_Lean_instHashableMVarId_hash(v_x_3394_);
    v___x_3397_ = lean_uint64_to_usize(v___x_3396_);
    v___x_3398_ = 1usize;
    v___x_3399_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg(v_x_3393_, v___x_3397_, v___x_3398_, v_x_3394_, v_x_3395_);
    return v___x_3399_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(
    mut v_mvarId_3400_: *mut LeanObject,
    mut v_val_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3412_: u8 = 0;
    let mut v_depth_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3436_: u8 = 0;
    let mut v_isSharedCheck_3437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3404_ = lean_st_ref_take(v___y_3402_);
                v_mctx_3405_ = lean_ctor_get(v___x_3404_, 0);
                v_cache_3406_ = lean_ctor_get(v___x_3404_, 1);
                v_zetaDeltaFVarIds_3407_ = lean_ctor_get(v___x_3404_, 2);
                v_postponed_3408_ = lean_ctor_get(v___x_3404_, 3);
                v_diag_3409_ = lean_ctor_get(v___x_3404_, 4);
                v_isSharedCheck_3437_ = (!lean_is_exclusive(v___x_3404_)) as u8;
                if v_isSharedCheck_3437_ == 0 {
                    v___x_3411_ = v___x_3404_;
                    v_isShared_3412_ = v_isSharedCheck_3437_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3409_);
                    lean_inc(v_postponed_3408_);
                    lean_inc(v_zetaDeltaFVarIds_3407_);
                    lean_inc(v_cache_3406_);
                    lean_inc(v_mctx_3405_);
                    lean_dec(v___x_3404_);
                    v___x_3411_ = lean_box(0);
                    v_isShared_3412_ = v_isSharedCheck_3437_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3413_ = lean_ctor_get(v_mctx_3405_, 0);
                v_levelAssignDepth_3414_ = lean_ctor_get(v_mctx_3405_, 1);
                v_lmvarCounter_3415_ = lean_ctor_get(v_mctx_3405_, 2);
                v_mvarCounter_3416_ = lean_ctor_get(v_mctx_3405_, 3);
                v_lDecls_3417_ = lean_ctor_get(v_mctx_3405_, 4);
                v_decls_3418_ = lean_ctor_get(v_mctx_3405_, 5);
                v_userNames_3419_ = lean_ctor_get(v_mctx_3405_, 6);
                v_lAssignment_3420_ = lean_ctor_get(v_mctx_3405_, 7);
                v_eAssignment_3421_ = lean_ctor_get(v_mctx_3405_, 8);
                v_dAssignment_3422_ = lean_ctor_get(v_mctx_3405_, 9);
                v_isSharedCheck_3436_ = (!lean_is_exclusive(v_mctx_3405_)) as u8;
                if v_isSharedCheck_3436_ == 0 {
                    v___x_3424_ = v_mctx_3405_;
                    v_isShared_3425_ = v_isSharedCheck_3436_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_3422_);
                    lean_inc(v_eAssignment_3421_);
                    lean_inc(v_lAssignment_3420_);
                    lean_inc(v_userNames_3419_);
                    lean_inc(v_decls_3418_);
                    lean_inc(v_lDecls_3417_);
                    lean_inc(v_mvarCounter_3416_);
                    lean_inc(v_lmvarCounter_3415_);
                    lean_inc(v_levelAssignDepth_3414_);
                    lean_inc(v_depth_3413_);
                    lean_dec(v_mctx_3405_);
                    v___x_3424_ = lean_box(0);
                    v_isShared_3425_ = v_isSharedCheck_3436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3426_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2___redArg(v_eAssignment_3421_, v_mvarId_3400_, v_val_3401_);
                if v_isShared_3425_ == 0 {
                    lean_ctor_set(v___x_3424_, 8, v___x_3426_);
                    v___x_3428_ = v___x_3424_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_depth_3413_);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 1, v_levelAssignDepth_3414_);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 2, v_lmvarCounter_3415_);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 3, v_mvarCounter_3416_);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 4, v_lDecls_3417_);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 5, v_decls_3418_);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 6, v_userNames_3419_);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 7, v_lAssignment_3420_);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 8, v___x_3426_);
                    lean_ctor_set(v_reuseFailAlloc_3435_, 9, v_dAssignment_3422_);
                    v___x_3428_ = v_reuseFailAlloc_3435_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3412_ == 0 {
                    lean_ctor_set(v___x_3411_, 0, v___x_3428_);
                    v___x_3430_ = v___x_3411_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3428_);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 1, v_cache_3406_);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 2, v_zetaDeltaFVarIds_3407_);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 3, v_postponed_3408_);
                    lean_ctor_set(v_reuseFailAlloc_3434_, 4, v_diag_3409_);
                    v___x_3430_ = v_reuseFailAlloc_3434_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3431_ = lean_st_ref_set(v___y_3402_, v___x_3430_);
                v___x_3432_ = lean_box(0);
                v___x_3433_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3433_, 0, v___x_3432_);
                return v___x_3433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg___boxed(
    mut v_mvarId_3438_: *mut LeanObject,
    mut v_val_3439_: *mut LeanObject,
    mut v___y_3440_: *mut LeanObject,
    mut v___y_3441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3442_: *mut LeanObject = core::ptr::null_mut();
    v_res_3442_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(v_mvarId_3438_, v_val_3439_, v___y_3440_);
    lean_dec(v___y_3440_);
    return v_res_3442_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__13_spec__17(
    mut v_mvarId_3443_: *mut LeanObject,
    mut v_as_3444_: *mut LeanObject,
    mut v_sz_3445_: usize,
    mut v_i_3446_: usize,
    mut v_b_3447_: *mut LeanObject,
    mut v___y_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
    mut v___y_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3458_: u8 = 0;
    let mut v_a_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: usize = 0;
    let mut v___x_3471_: usize = 0;
    let mut v_a_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3478_: u8 = 0;
    let mut v_fst_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3483_: u8 = 0;
    let mut v_posMap_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negMap_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: u8 = 0;
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negMap_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3508_: u8 = 0;
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3528_: u8 = 0;
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3532_: u8 = 0;
    let mut v_a_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3540_: u8 = 0;
    let mut v_a_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3544_: u8 = 0;
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3548_: u8 = 0;
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3555_: u8 = 0;
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v_val_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3563_: u8 = 0;
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3568_: u8 = 0;
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3588_: u8 = 0;
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3592_: u8 = 0;
    let mut v_a_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3596_: u8 = 0;
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut v_a_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3604_: u8 = 0;
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v_isSharedCheck_3609_: u8 = 0;
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3612_: u8 = 0;
    let mut v_a_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3616_: u8 = 0;
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3620_: u8 = 0;
    let mut v_isSharedCheck_3621_: u8 = 0;
    let mut v_isSharedCheck_3622_: u8 = 0;
    let mut v_isSharedCheck_3623_: u8 = 0;
    let mut v_unused_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3453_ = lean_usize_dec_lt(v_i_3446_, v_sz_3445_);
                if v___x_3453_ == 0 {
                    lean_dec(v_mvarId_3443_);
                    v___x_3454_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3454_, 0, v_b_3447_);
                    return v___x_3454_;
                } else {
                    v_snd_3455_ = lean_ctor_get(v_b_3447_, 1);
                    v_isSharedCheck_3623_ = (!lean_is_exclusive(v_b_3447_)) as u8;
                    if v_isSharedCheck_3623_ == 0 {
                        v_unused_3624_ = lean_ctor_get(v_b_3447_, 0);
                        lean_dec(v_unused_3624_);
                        v___x_3457_ = v_b_3447_;
                        v_isShared_3458_ = v_isSharedCheck_3623_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3455_);
                        lean_dec(v_b_3447_);
                        v___x_3457_ = lean_box(0);
                        v_isShared_3458_ = v_isSharedCheck_3623_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3466_ = lean_box(0);
                v_a_3473_ = lean_array_uget(v_as_3444_, v_i_3446_);
                if lean_obj_tag(v_a_3473_) == 0 {
                    lean_del_object(v___x_3457_);
                    v_a_3468_ = v_snd_3455_;
                    state = 4;
                    continue;
                } else {
                    v_snd_3474_ = lean_ctor_get(v_snd_3455_, 1);
                    lean_inc(v_snd_3474_);
                    v_val_3475_ = lean_ctor_get(v_a_3473_, 0);
                    v_isSharedCheck_3622_ = (!lean_is_exclusive(v_a_3473_)) as u8;
                    if v_isSharedCheck_3622_ == 0 {
                        v___x_3477_ = v_a_3473_;
                        v_isShared_3478_ = v_isSharedCheck_3622_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_3475_);
                        lean_dec(v_a_3473_);
                        v___x_3477_ = lean_box(0);
                        v_isShared_3478_ = v_isSharedCheck_3622_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3461_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3461_, 0, v_a_3460_);
                if v_isShared_3458_ == 0 {
                    lean_ctor_set(v___x_3457_, 0, v___x_3461_);
                    v___x_3463_ = v___x_3457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3461_);
                    lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_snd_3455_);
                    v___x_3463_ = v_reuseFailAlloc_3465_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3464_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3464_, 0, v___x_3463_);
                return v___x_3464_;
            }
            4 => {
                v___x_3469_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3469_, 0, v___x_3466_);
                lean_ctor_set(v___x_3469_, 1, v_a_3468_);
                v___x_3470_ = 1usize;
                v___x_3471_ = lean_usize_add(v_i_3446_, v___x_3470_);
                v_i_3446_ = v___x_3471_;
                v_b_3447_ = v___x_3469_;
                state = 0;
                continue;
            }
            5 => {
                v_fst_3479_ = lean_ctor_get(v_snd_3474_, 0);
                v_snd_3480_ = lean_ctor_get(v_snd_3474_, 1);
                v_isSharedCheck_3621_ = (!lean_is_exclusive(v_snd_3474_)) as u8;
                if v_isSharedCheck_3621_ == 0 {
                    v___x_3482_ = v_snd_3474_;
                    v_isShared_3483_ = v_isSharedCheck_3621_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_snd_3480_);
                    lean_inc(v_fst_3479_);
                    lean_dec(v_snd_3474_);
                    v___x_3482_ = lean_box(0);
                    v_isShared_3483_ = v_isSharedCheck_3621_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3491_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3475_);
                if v___x_3491_ == 0 {
                    v___x_3492_ = l_Lean_LocalDecl_type(v_val_3475_);
                    lean_inc_ref(v___x_3492_);
                    v___x_3493_ = l_Lean_Meta_matchNot_x3f(
                        v___x_3492_,
                        v___y_3448_,
                        v___y_3449_,
                        v___y_3450_,
                        v___y_3451_,
                    );
                    if lean_obj_tag(v___x_3493_) == 0 {
                        v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
                        lean_inc(v_a_3494_);
                        lean_dec_ref_known(v___x_3493_, 1);
                        if lean_obj_tag(v_a_3494_) == 1 {
                            v_val_3560_ = lean_ctor_get(v_a_3494_, 0);
                            v_isSharedCheck_3612_ = (!lean_is_exclusive(v_a_3494_)) as u8;
                            if v_isSharedCheck_3612_ == 0 {
                                v___x_3562_ = v_a_3494_;
                                v_isShared_3563_ = v_isSharedCheck_3612_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_val_3560_);
                                lean_dec(v_a_3494_);
                                v___x_3562_ = lean_box(0);
                                v_isShared_3563_ = v_isSharedCheck_3612_;
                                state = 21;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3494_);
                            v_negMap_3496_ = v_snd_3480_;
                            v___y_3497_ = v___y_3448_;
                            v___y_3498_ = v___y_3449_;
                            v___y_3499_ = v___y_3450_;
                            v___y_3500_ = v___y_3451_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3492_);
                        lean_del_object(v___x_3482_);
                        lean_dec(v_snd_3480_);
                        lean_dec(v_fst_3479_);
                        lean_del_object(v___x_3477_);
                        lean_dec(v_val_3475_);
                        lean_del_object(v___x_3457_);
                        lean_dec(v_snd_3455_);
                        lean_dec(v_mvarId_3443_);
                        v_a_3613_ = lean_ctor_get(v___x_3493_, 0);
                        v_isSharedCheck_3620_ = (!lean_is_exclusive(v___x_3493_)) as u8;
                        if v_isSharedCheck_3620_ == 0 {
                            v___x_3615_ = v___x_3493_;
                            v_isShared_3616_ = v_isSharedCheck_3620_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_3613_);
                            lean_dec(v___x_3493_);
                            v___x_3615_ = lean_box(0);
                            v_isShared_3616_ = v_isSharedCheck_3620_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3477_);
                    lean_dec(v_val_3475_);
                    lean_del_object(v___x_3457_);
                    lean_dec(v_snd_3455_);
                    v_posMap_3485_ = v_fst_3479_;
                    v_negMap_3486_ = v_snd_3480_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3483_ == 0 {
                    lean_ctor_set(v___x_3482_, 1, v_negMap_3486_);
                    lean_ctor_set(v___x_3482_, 0, v_posMap_3485_);
                    v___x_3488_ = v___x_3482_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_posMap_3485_);
                    lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_negMap_3486_);
                    v___x_3488_ = v_reuseFailAlloc_3490_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3489_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3489_, 0, v___x_3466_);
                lean_ctor_set(v___x_3489_, 1, v___x_3488_);
                v_a_3468_ = v___x_3489_;
                state = 4;
                continue;
            }
            9 => {
                lean_inc_ref(v___x_3492_);
                v___x_3501_ = l_Lean_Meta_isProp(
                    v___x_3492_,
                    v___y_3497_,
                    v___y_3498_,
                    v___y_3499_,
                    v___y_3500_,
                );
                if lean_obj_tag(v___x_3501_) == 0 {
                    v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
                    lean_inc(v_a_3502_);
                    lean_dec_ref_known(v___x_3501_, 1);
                    v___x_3503_ = (lean_unbox(v_a_3502_) as u8);
                    lean_dec(v_a_3502_);
                    if v___x_3503_ == 0 {
                        lean_dec_ref(v___x_3492_);
                        lean_del_object(v___x_3477_);
                        lean_dec(v_val_3475_);
                        lean_del_object(v___x_3457_);
                        lean_dec(v_snd_3455_);
                        v_posMap_3485_ = v_fst_3479_;
                        v_negMap_3486_ = v_negMap_3496_;
                        state = 7;
                        continue;
                    } else {
                        v___x_3504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(v_negMap_3496_, v___x_3492_);
                        if lean_obj_tag(v___x_3504_) == 1 {
                            lean_dec_ref(v___x_3492_);
                            lean_del_object(v___x_3482_);
                            v_val_3505_ = lean_ctor_get(v___x_3504_, 0);
                            v_isSharedCheck_3549_ = (!lean_is_exclusive(v___x_3504_)) as u8;
                            if v_isSharedCheck_3549_ == 0 {
                                v___x_3507_ = v___x_3504_;
                                v_isShared_3508_ = v_isSharedCheck_3549_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_val_3505_);
                                lean_dec(v___x_3504_);
                                v___x_3507_ = lean_box(0);
                                v_isShared_3508_ = v_isSharedCheck_3549_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3504_);
                            lean_del_object(v___x_3477_);
                            lean_del_object(v___x_3457_);
                            lean_dec(v_snd_3455_);
                            v___x_3550_ = l_Lean_LocalDecl_fvarId(v_val_3475_);
                            lean_dec(v_val_3475_);
                            v___x_3551_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2___redArg(v_fst_3479_, v___x_3492_, v___x_3550_);
                            v_posMap_3485_ = v___x_3551_;
                            v_negMap_3486_ = v_negMap_3496_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_negMap_3496_);
                    lean_dec_ref(v___x_3492_);
                    lean_del_object(v___x_3482_);
                    lean_dec(v_fst_3479_);
                    lean_del_object(v___x_3477_);
                    lean_dec(v_val_3475_);
                    lean_del_object(v___x_3457_);
                    lean_dec(v_snd_3455_);
                    lean_dec(v_mvarId_3443_);
                    v_a_3552_ = lean_ctor_get(v___x_3501_, 0);
                    v_isSharedCheck_3559_ = (!lean_is_exclusive(v___x_3501_)) as u8;
                    if v_isSharedCheck_3559_ == 0 {
                        v___x_3554_ = v___x_3501_;
                        v_isShared_3555_ = v_isSharedCheck_3559_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_3552_);
                        lean_dec(v___x_3501_);
                        v___x_3554_ = lean_box(0);
                        v_isShared_3555_ = v_isSharedCheck_3559_;
                        state = 19;
                        continue;
                    }
                }
            }
            10 => {
                lean_inc(v_mvarId_3443_);
                v___x_3509_ = l_Lean_MVarId_getType(
                    v_mvarId_3443_,
                    v___y_3497_,
                    v___y_3498_,
                    v___y_3499_,
                    v___y_3500_,
                );
                if lean_obj_tag(v___x_3509_) == 0 {
                    v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
                    lean_inc(v_a_3510_);
                    lean_dec_ref_known(v___x_3509_, 1);
                    v___x_3511_ = l_Lean_LocalDecl_toExpr(v_val_3475_);
                    v___x_3512_ = l_Lean_mkFVar(v_val_3505_);
                    v___x_3513_ = l_Lean_Meta_mkAbsurd(
                        v_a_3510_,
                        v___x_3511_,
                        v___x_3512_,
                        v___y_3497_,
                        v___y_3498_,
                        v___y_3499_,
                        v___y_3500_,
                    );
                    if lean_obj_tag(v___x_3513_) == 0 {
                        v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
                        lean_inc(v_a_3514_);
                        lean_dec_ref_known(v___x_3513_, 1);
                        v___x_3515_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(v_mvarId_3443_, v_a_3514_, v___y_3498_);
                        if lean_obj_tag(v___x_3515_) == 0 {
                            lean_dec_ref_known(v___x_3515_, 1);
                            v___x_3516_ = lean_box((v___x_3453_) as usize);
                            if v_isShared_3508_ == 0 {
                                lean_ctor_set(v___x_3507_, 0, v___x_3516_);
                                v___x_3518_ = v___x_3507_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3516_);
                                v___x_3518_ = v_reuseFailAlloc_3524_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3507_);
                            lean_dec_ref(v_negMap_3496_);
                            lean_dec(v_fst_3479_);
                            lean_del_object(v___x_3477_);
                            lean_del_object(v___x_3457_);
                            lean_dec(v_snd_3455_);
                            v_a_3525_ = lean_ctor_get(v___x_3515_, 0);
                            v_isSharedCheck_3532_ = (!lean_is_exclusive(v___x_3515_)) as u8;
                            if v_isSharedCheck_3532_ == 0 {
                                v___x_3527_ = v___x_3515_;
                                v_isShared_3528_ = v_isSharedCheck_3532_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_3525_);
                                lean_dec(v___x_3515_);
                                v___x_3527_ = lean_box(0);
                                v_isShared_3528_ = v_isSharedCheck_3532_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_3507_);
                        lean_dec_ref(v_negMap_3496_);
                        lean_dec(v_fst_3479_);
                        lean_del_object(v___x_3477_);
                        lean_del_object(v___x_3457_);
                        lean_dec(v_snd_3455_);
                        lean_dec(v_mvarId_3443_);
                        v_a_3533_ = lean_ctor_get(v___x_3513_, 0);
                        v_isSharedCheck_3540_ = (!lean_is_exclusive(v___x_3513_)) as u8;
                        if v_isSharedCheck_3540_ == 0 {
                            v___x_3535_ = v___x_3513_;
                            v_isShared_3536_ = v_isSharedCheck_3540_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_3533_);
                            lean_dec(v___x_3513_);
                            v___x_3535_ = lean_box(0);
                            v_isShared_3536_ = v_isSharedCheck_3540_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3507_);
                    lean_dec(v_val_3505_);
                    lean_dec_ref(v_negMap_3496_);
                    lean_dec(v_fst_3479_);
                    lean_del_object(v___x_3477_);
                    lean_dec(v_val_3475_);
                    lean_del_object(v___x_3457_);
                    lean_dec(v_snd_3455_);
                    lean_dec(v_mvarId_3443_);
                    v_a_3541_ = lean_ctor_get(v___x_3509_, 0);
                    v_isSharedCheck_3548_ = (!lean_is_exclusive(v___x_3509_)) as u8;
                    if v_isSharedCheck_3548_ == 0 {
                        v___x_3543_ = v___x_3509_;
                        v_isShared_3544_ = v_isSharedCheck_3548_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3541_);
                        lean_dec(v___x_3509_);
                        v___x_3543_ = lean_box(0);
                        v_isShared_3544_ = v_isSharedCheck_3548_;
                        state = 17;
                        continue;
                    }
                }
            }
            11 => {
                v___x_3519_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3519_, 0, v_fst_3479_);
                lean_ctor_set(v___x_3519_, 1, v_negMap_3496_);
                v___x_3520_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3520_, 0, v___x_3518_);
                lean_ctor_set(v___x_3520_, 1, v___x_3519_);
                if v_isShared_3478_ == 0 {
                    lean_ctor_set_tag(v___x_3477_, 0);
                    lean_ctor_set(v___x_3477_, 0, v___x_3520_);
                    v___x_3522_ = v___x_3477_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3520_);
                    v___x_3522_ = v_reuseFailAlloc_3523_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_a_3460_ = v___x_3522_;
                state = 2;
                continue;
            }
            13 => {
                if v_isShared_3528_ == 0 {
                    v___x_3530_ = v___x_3527_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
                    v___x_3530_ = v_reuseFailAlloc_3531_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3530_;
            }
            15 => {
                if v_isShared_3536_ == 0 {
                    v___x_3538_ = v___x_3535_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
                    v___x_3538_ = v_reuseFailAlloc_3539_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3538_;
            }
            17 => {
                if v_isShared_3544_ == 0 {
                    v___x_3546_ = v___x_3543_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
                    v___x_3546_ = v_reuseFailAlloc_3547_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3546_;
            }
            19 => {
                if v_isShared_3555_ == 0 {
                    v___x_3557_ = v___x_3554_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
                    v___x_3557_ = v_reuseFailAlloc_3558_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3557_;
            }
            21 => {
                v___x_3564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(v_fst_3479_, v_val_3560_);
                if lean_obj_tag(v___x_3564_) == 1 {
                    lean_dec(v_val_3560_);
                    lean_dec_ref(v___x_3492_);
                    lean_del_object(v___x_3482_);
                    lean_del_object(v___x_3477_);
                    v_val_3565_ = lean_ctor_get(v___x_3564_, 0);
                    v_isSharedCheck_3609_ = (!lean_is_exclusive(v___x_3564_)) as u8;
                    if v_isSharedCheck_3609_ == 0 {
                        v___x_3567_ = v___x_3564_;
                        v_isShared_3568_ = v_isSharedCheck_3609_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_val_3565_);
                        lean_dec(v___x_3564_);
                        v___x_3567_ = lean_box(0);
                        v_isShared_3568_ = v_isSharedCheck_3609_;
                        state = 22;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3564_);
                    lean_del_object(v___x_3562_);
                    v___x_3610_ = l_Lean_LocalDecl_fvarId(v_val_3475_);
                    v___x_3611_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2___redArg(v_snd_3480_, v_val_3560_, v___x_3610_);
                    v_negMap_3496_ = v___x_3611_;
                    v___y_3497_ = v___y_3448_;
                    v___y_3498_ = v___y_3449_;
                    v___y_3499_ = v___y_3450_;
                    v___y_3500_ = v___y_3451_;
                    state = 9;
                    continue;
                }
            }
            22 => {
                lean_inc(v_mvarId_3443_);
                v___x_3569_ = l_Lean_MVarId_getType(
                    v_mvarId_3443_,
                    v___y_3448_,
                    v___y_3449_,
                    v___y_3450_,
                    v___y_3451_,
                );
                if lean_obj_tag(v___x_3569_) == 0 {
                    v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
                    lean_inc(v_a_3570_);
                    lean_dec_ref_known(v___x_3569_, 1);
                    v___x_3571_ = l_Lean_mkFVar(v_val_3565_);
                    v___x_3572_ = l_Lean_LocalDecl_toExpr(v_val_3475_);
                    v___x_3573_ = l_Lean_Meta_mkAbsurd(
                        v_a_3570_,
                        v___x_3571_,
                        v___x_3572_,
                        v___y_3448_,
                        v___y_3449_,
                        v___y_3450_,
                        v___y_3451_,
                    );
                    if lean_obj_tag(v___x_3573_) == 0 {
                        v_a_3574_ = lean_ctor_get(v___x_3573_, 0);
                        lean_inc(v_a_3574_);
                        lean_dec_ref_known(v___x_3573_, 1);
                        v___x_3575_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(v_mvarId_3443_, v_a_3574_, v___y_3449_);
                        if lean_obj_tag(v___x_3575_) == 0 {
                            lean_dec_ref_known(v___x_3575_, 1);
                            v___x_3576_ = lean_box((v___x_3453_) as usize);
                            if v_isShared_3568_ == 0 {
                                lean_ctor_set(v___x_3567_, 0, v___x_3576_);
                                v___x_3578_ = v___x_3567_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3576_);
                                v___x_3578_ = v_reuseFailAlloc_3584_;
                                state = 23;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3567_);
                            lean_del_object(v___x_3562_);
                            lean_dec(v_snd_3480_);
                            lean_dec(v_fst_3479_);
                            lean_del_object(v___x_3457_);
                            lean_dec(v_snd_3455_);
                            v_a_3585_ = lean_ctor_get(v___x_3575_, 0);
                            v_isSharedCheck_3592_ = (!lean_is_exclusive(v___x_3575_)) as u8;
                            if v_isSharedCheck_3592_ == 0 {
                                v___x_3587_ = v___x_3575_;
                                v_isShared_3588_ = v_isSharedCheck_3592_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_3585_);
                                lean_dec(v___x_3575_);
                                v___x_3587_ = lean_box(0);
                                v_isShared_3588_ = v_isSharedCheck_3592_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_3567_);
                        lean_del_object(v___x_3562_);
                        lean_dec(v_snd_3480_);
                        lean_dec(v_fst_3479_);
                        lean_del_object(v___x_3457_);
                        lean_dec(v_snd_3455_);
                        lean_dec(v_mvarId_3443_);
                        v_a_3593_ = lean_ctor_get(v___x_3573_, 0);
                        v_isSharedCheck_3600_ = (!lean_is_exclusive(v___x_3573_)) as u8;
                        if v_isSharedCheck_3600_ == 0 {
                            v___x_3595_ = v___x_3573_;
                            v_isShared_3596_ = v_isSharedCheck_3600_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_3593_);
                            lean_dec(v___x_3573_);
                            v___x_3595_ = lean_box(0);
                            v_isShared_3596_ = v_isSharedCheck_3600_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3567_);
                    lean_dec(v_val_3565_);
                    lean_del_object(v___x_3562_);
                    lean_dec(v_snd_3480_);
                    lean_dec(v_fst_3479_);
                    lean_dec(v_val_3475_);
                    lean_del_object(v___x_3457_);
                    lean_dec(v_snd_3455_);
                    lean_dec(v_mvarId_3443_);
                    v_a_3601_ = lean_ctor_get(v___x_3569_, 0);
                    v_isSharedCheck_3608_ = (!lean_is_exclusive(v___x_3569_)) as u8;
                    if v_isSharedCheck_3608_ == 0 {
                        v___x_3603_ = v___x_3569_;
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_a_3601_);
                        lean_dec(v___x_3569_);
                        v___x_3603_ = lean_box(0);
                        v_isShared_3604_ = v_isSharedCheck_3608_;
                        state = 29;
                        continue;
                    }
                }
            }
            23 => {
                v___x_3579_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3579_, 0, v_fst_3479_);
                lean_ctor_set(v___x_3579_, 1, v_snd_3480_);
                v___x_3580_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3580_, 0, v___x_3578_);
                lean_ctor_set(v___x_3580_, 1, v___x_3579_);
                if v_isShared_3563_ == 0 {
                    lean_ctor_set_tag(v___x_3562_, 0);
                    lean_ctor_set(v___x_3562_, 0, v___x_3580_);
                    v___x_3582_ = v___x_3562_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3580_);
                    v___x_3582_ = v_reuseFailAlloc_3583_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_a_3460_ = v___x_3582_;
                state = 2;
                continue;
            }
            25 => {
                if v_isShared_3588_ == 0 {
                    v___x_3590_ = v___x_3587_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
                    v___x_3590_ = v_reuseFailAlloc_3591_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3590_;
            }
            27 => {
                if v_isShared_3596_ == 0 {
                    v___x_3598_ = v___x_3595_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
                    v___x_3598_ = v_reuseFailAlloc_3599_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3598_;
            }
            29 => {
                if v_isShared_3604_ == 0 {
                    v___x_3606_ = v___x_3603_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3601_);
                    v___x_3606_ = v_reuseFailAlloc_3607_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3606_;
            }
            31 => {
                if v_isShared_3616_ == 0 {
                    v___x_3618_ = v___x_3615_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3613_);
                    v___x_3618_ = v_reuseFailAlloc_3619_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__13_spec__17___boxed(
    mut v_mvarId_3625_: *mut LeanObject,
    mut v_as_3626_: *mut LeanObject,
    mut v_sz_3627_: *mut LeanObject,
    mut v_i_3628_: *mut LeanObject,
    mut v_b_3629_: *mut LeanObject,
    mut v___y_3630_: *mut LeanObject,
    mut v___y_3631_: *mut LeanObject,
    mut v___y_3632_: *mut LeanObject,
    mut v___y_3633_: *mut LeanObject,
    mut v___y_3634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3635_: usize = 0;
    let mut v_i_boxed_3636_: usize = 0;
    let mut v_res_3637_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3635_ = lean_unbox_usize(v_sz_3627_);
    lean_dec(v_sz_3627_);
    v_i_boxed_3636_ = lean_unbox_usize(v_i_3628_);
    lean_dec(v_i_3628_);
    v_res_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__13_spec__17(v_mvarId_3625_, v_as_3626_, v_sz_boxed_3635_, v_i_boxed_3636_, v_b_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
    lean_dec(v___y_3633_);
    lean_dec_ref(v___y_3632_);
    lean_dec(v___y_3631_);
    lean_dec_ref(v___y_3630_);
    lean_dec_ref(v_as_3626_);
    return v_res_3637_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__13(
    mut v_mvarId_3638_: *mut LeanObject,
    mut v_as_3639_: *mut LeanObject,
    mut v_sz_3640_: usize,
    mut v_i_3641_: usize,
    mut v_b_3642_: *mut LeanObject,
    mut v___y_3643_: *mut LeanObject,
    mut v___y_3644_: *mut LeanObject,
    mut v___y_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3648_: u8 = 0;
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v_a_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: usize = 0;
    let mut v___x_3666_: usize = 0;
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3673_: u8 = 0;
    let mut v_fst_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3678_: u8 = 0;
    let mut v_posMap_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negMap_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: u8 = 0;
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negMap_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: u8 = 0;
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3703_: u8 = 0;
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3723_: u8 = 0;
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3727_: u8 = 0;
    let mut v_a_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3731_: u8 = 0;
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut v_a_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3739_: u8 = 0;
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v_isSharedCheck_3744_: u8 = 0;
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3750_: u8 = 0;
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut v_val_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3758_: u8 = 0;
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3763_: u8 = 0;
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3783_: u8 = 0;
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut v_a_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut v_a_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3799_: u8 = 0;
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_isSharedCheck_3804_: u8 = 0;
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3807_: u8 = 0;
    let mut v_a_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3815_: u8 = 0;
    let mut v_isSharedCheck_3816_: u8 = 0;
    let mut v_isSharedCheck_3817_: u8 = 0;
    let mut v_isSharedCheck_3818_: u8 = 0;
    let mut v_unused_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3648_ = lean_usize_dec_lt(v_i_3641_, v_sz_3640_);
                if v___x_3648_ == 0 {
                    lean_dec(v_mvarId_3638_);
                    v___x_3649_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3649_, 0, v_b_3642_);
                    return v___x_3649_;
                } else {
                    v_snd_3650_ = lean_ctor_get(v_b_3642_, 1);
                    v_isSharedCheck_3818_ = (!lean_is_exclusive(v_b_3642_)) as u8;
                    if v_isSharedCheck_3818_ == 0 {
                        v_unused_3819_ = lean_ctor_get(v_b_3642_, 0);
                        lean_dec(v_unused_3819_);
                        v___x_3652_ = v_b_3642_;
                        v_isShared_3653_ = v_isSharedCheck_3818_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3650_);
                        lean_dec(v_b_3642_);
                        v___x_3652_ = lean_box(0);
                        v_isShared_3653_ = v_isSharedCheck_3818_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3661_ = lean_box(0);
                v_a_3668_ = lean_array_uget(v_as_3639_, v_i_3641_);
                if lean_obj_tag(v_a_3668_) == 0 {
                    lean_del_object(v___x_3652_);
                    v_a_3663_ = v_snd_3650_;
                    state = 4;
                    continue;
                } else {
                    v_snd_3669_ = lean_ctor_get(v_snd_3650_, 1);
                    lean_inc(v_snd_3669_);
                    v_val_3670_ = lean_ctor_get(v_a_3668_, 0);
                    v_isSharedCheck_3817_ = (!lean_is_exclusive(v_a_3668_)) as u8;
                    if v_isSharedCheck_3817_ == 0 {
                        v___x_3672_ = v_a_3668_;
                        v_isShared_3673_ = v_isSharedCheck_3817_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_3670_);
                        lean_dec(v_a_3668_);
                        v___x_3672_ = lean_box(0);
                        v_isShared_3673_ = v_isSharedCheck_3817_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3656_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3656_, 0, v_a_3655_);
                if v_isShared_3653_ == 0 {
                    lean_ctor_set(v___x_3652_, 0, v___x_3656_);
                    v___x_3658_ = v___x_3652_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3656_);
                    lean_ctor_set(v_reuseFailAlloc_3660_, 1, v_snd_3650_);
                    v___x_3658_ = v_reuseFailAlloc_3660_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3659_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3659_, 0, v___x_3658_);
                return v___x_3659_;
            }
            4 => {
                v___x_3664_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3664_, 0, v___x_3661_);
                lean_ctor_set(v___x_3664_, 1, v_a_3663_);
                v___x_3665_ = 1usize;
                v___x_3666_ = lean_usize_add(v_i_3641_, v___x_3665_);
                v___x_3667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__13_spec__17(v_mvarId_3638_, v_as_3639_, v_sz_3640_, v___x_3666_, v___x_3664_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
                return v___x_3667_;
            }
            5 => {
                v_fst_3674_ = lean_ctor_get(v_snd_3669_, 0);
                v_snd_3675_ = lean_ctor_get(v_snd_3669_, 1);
                v_isSharedCheck_3816_ = (!lean_is_exclusive(v_snd_3669_)) as u8;
                if v_isSharedCheck_3816_ == 0 {
                    v___x_3677_ = v_snd_3669_;
                    v_isShared_3678_ = v_isSharedCheck_3816_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_snd_3675_);
                    lean_inc(v_fst_3674_);
                    lean_dec(v_snd_3669_);
                    v___x_3677_ = lean_box(0);
                    v_isShared_3678_ = v_isSharedCheck_3816_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3686_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3670_);
                if v___x_3686_ == 0 {
                    v___x_3687_ = l_Lean_LocalDecl_type(v_val_3670_);
                    lean_inc_ref(v___x_3687_);
                    v___x_3688_ = l_Lean_Meta_matchNot_x3f(
                        v___x_3687_,
                        v___y_3643_,
                        v___y_3644_,
                        v___y_3645_,
                        v___y_3646_,
                    );
                    if lean_obj_tag(v___x_3688_) == 0 {
                        v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
                        lean_inc(v_a_3689_);
                        lean_dec_ref_known(v___x_3688_, 1);
                        if lean_obj_tag(v_a_3689_) == 1 {
                            v_val_3755_ = lean_ctor_get(v_a_3689_, 0);
                            v_isSharedCheck_3807_ = (!lean_is_exclusive(v_a_3689_)) as u8;
                            if v_isSharedCheck_3807_ == 0 {
                                v___x_3757_ = v_a_3689_;
                                v_isShared_3758_ = v_isSharedCheck_3807_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_val_3755_);
                                lean_dec(v_a_3689_);
                                v___x_3757_ = lean_box(0);
                                v_isShared_3758_ = v_isSharedCheck_3807_;
                                state = 21;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3689_);
                            v_negMap_3691_ = v_snd_3675_;
                            v___y_3692_ = v___y_3643_;
                            v___y_3693_ = v___y_3644_;
                            v___y_3694_ = v___y_3645_;
                            v___y_3695_ = v___y_3646_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_3687_);
                        lean_del_object(v___x_3677_);
                        lean_dec(v_snd_3675_);
                        lean_dec(v_fst_3674_);
                        lean_del_object(v___x_3672_);
                        lean_dec(v_val_3670_);
                        lean_del_object(v___x_3652_);
                        lean_dec(v_snd_3650_);
                        lean_dec(v_mvarId_3638_);
                        v_a_3808_ = lean_ctor_get(v___x_3688_, 0);
                        v_isSharedCheck_3815_ = (!lean_is_exclusive(v___x_3688_)) as u8;
                        if v_isSharedCheck_3815_ == 0 {
                            v___x_3810_ = v___x_3688_;
                            v_isShared_3811_ = v_isSharedCheck_3815_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_3808_);
                            lean_dec(v___x_3688_);
                            v___x_3810_ = lean_box(0);
                            v_isShared_3811_ = v_isSharedCheck_3815_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3672_);
                    lean_dec(v_val_3670_);
                    lean_del_object(v___x_3652_);
                    lean_dec(v_snd_3650_);
                    v_posMap_3680_ = v_fst_3674_;
                    v_negMap_3681_ = v_snd_3675_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3678_ == 0 {
                    lean_ctor_set(v___x_3677_, 1, v_negMap_3681_);
                    lean_ctor_set(v___x_3677_, 0, v_posMap_3680_);
                    v___x_3683_ = v___x_3677_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_posMap_3680_);
                    lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_negMap_3681_);
                    v___x_3683_ = v_reuseFailAlloc_3685_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3684_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3684_, 0, v___x_3661_);
                lean_ctor_set(v___x_3684_, 1, v___x_3683_);
                v_a_3663_ = v___x_3684_;
                state = 4;
                continue;
            }
            9 => {
                lean_inc_ref(v___x_3687_);
                v___x_3696_ = l_Lean_Meta_isProp(
                    v___x_3687_,
                    v___y_3692_,
                    v___y_3693_,
                    v___y_3694_,
                    v___y_3695_,
                );
                if lean_obj_tag(v___x_3696_) == 0 {
                    v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
                    lean_inc(v_a_3697_);
                    lean_dec_ref_known(v___x_3696_, 1);
                    v___x_3698_ = (lean_unbox(v_a_3697_) as u8);
                    lean_dec(v_a_3697_);
                    if v___x_3698_ == 0 {
                        lean_dec_ref(v___x_3687_);
                        lean_del_object(v___x_3672_);
                        lean_dec(v_val_3670_);
                        lean_del_object(v___x_3652_);
                        lean_dec(v_snd_3650_);
                        v_posMap_3680_ = v_fst_3674_;
                        v_negMap_3681_ = v_negMap_3691_;
                        state = 7;
                        continue;
                    } else {
                        v___x_3699_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(v_negMap_3691_, v___x_3687_);
                        if lean_obj_tag(v___x_3699_) == 1 {
                            lean_dec_ref(v___x_3687_);
                            lean_del_object(v___x_3677_);
                            v_val_3700_ = lean_ctor_get(v___x_3699_, 0);
                            v_isSharedCheck_3744_ = (!lean_is_exclusive(v___x_3699_)) as u8;
                            if v_isSharedCheck_3744_ == 0 {
                                v___x_3702_ = v___x_3699_;
                                v_isShared_3703_ = v_isSharedCheck_3744_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_val_3700_);
                                lean_dec(v___x_3699_);
                                v___x_3702_ = lean_box(0);
                                v_isShared_3703_ = v_isSharedCheck_3744_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3699_);
                            lean_del_object(v___x_3672_);
                            lean_del_object(v___x_3652_);
                            lean_dec(v_snd_3650_);
                            v___x_3745_ = l_Lean_LocalDecl_fvarId(v_val_3670_);
                            lean_dec(v_val_3670_);
                            v___x_3746_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2___redArg(v_fst_3674_, v___x_3687_, v___x_3745_);
                            v_posMap_3680_ = v___x_3746_;
                            v_negMap_3681_ = v_negMap_3691_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_negMap_3691_);
                    lean_dec_ref(v___x_3687_);
                    lean_del_object(v___x_3677_);
                    lean_dec(v_fst_3674_);
                    lean_del_object(v___x_3672_);
                    lean_dec(v_val_3670_);
                    lean_del_object(v___x_3652_);
                    lean_dec(v_snd_3650_);
                    lean_dec(v_mvarId_3638_);
                    v_a_3747_ = lean_ctor_get(v___x_3696_, 0);
                    v_isSharedCheck_3754_ = (!lean_is_exclusive(v___x_3696_)) as u8;
                    if v_isSharedCheck_3754_ == 0 {
                        v___x_3749_ = v___x_3696_;
                        v_isShared_3750_ = v_isSharedCheck_3754_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_3747_);
                        lean_dec(v___x_3696_);
                        v___x_3749_ = lean_box(0);
                        v_isShared_3750_ = v_isSharedCheck_3754_;
                        state = 19;
                        continue;
                    }
                }
            }
            10 => {
                lean_inc(v_mvarId_3638_);
                v___x_3704_ = l_Lean_MVarId_getType(
                    v_mvarId_3638_,
                    v___y_3692_,
                    v___y_3693_,
                    v___y_3694_,
                    v___y_3695_,
                );
                if lean_obj_tag(v___x_3704_) == 0 {
                    v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
                    lean_inc(v_a_3705_);
                    lean_dec_ref_known(v___x_3704_, 1);
                    v___x_3706_ = l_Lean_LocalDecl_toExpr(v_val_3670_);
                    v___x_3707_ = l_Lean_mkFVar(v_val_3700_);
                    v___x_3708_ = l_Lean_Meta_mkAbsurd(
                        v_a_3705_,
                        v___x_3706_,
                        v___x_3707_,
                        v___y_3692_,
                        v___y_3693_,
                        v___y_3694_,
                        v___y_3695_,
                    );
                    if lean_obj_tag(v___x_3708_) == 0 {
                        v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
                        lean_inc(v_a_3709_);
                        lean_dec_ref_known(v___x_3708_, 1);
                        v___x_3710_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(v_mvarId_3638_, v_a_3709_, v___y_3693_);
                        if lean_obj_tag(v___x_3710_) == 0 {
                            lean_dec_ref_known(v___x_3710_, 1);
                            v___x_3711_ = lean_box((v___x_3648_) as usize);
                            if v_isShared_3703_ == 0 {
                                lean_ctor_set(v___x_3702_, 0, v___x_3711_);
                                v___x_3713_ = v___x_3702_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3711_);
                                v___x_3713_ = v_reuseFailAlloc_3719_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3702_);
                            lean_dec_ref(v_negMap_3691_);
                            lean_dec(v_fst_3674_);
                            lean_del_object(v___x_3672_);
                            lean_del_object(v___x_3652_);
                            lean_dec(v_snd_3650_);
                            v_a_3720_ = lean_ctor_get(v___x_3710_, 0);
                            v_isSharedCheck_3727_ = (!lean_is_exclusive(v___x_3710_)) as u8;
                            if v_isSharedCheck_3727_ == 0 {
                                v___x_3722_ = v___x_3710_;
                                v_isShared_3723_ = v_isSharedCheck_3727_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_3720_);
                                lean_dec(v___x_3710_);
                                v___x_3722_ = lean_box(0);
                                v_isShared_3723_ = v_isSharedCheck_3727_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_3702_);
                        lean_dec_ref(v_negMap_3691_);
                        lean_dec(v_fst_3674_);
                        lean_del_object(v___x_3672_);
                        lean_del_object(v___x_3652_);
                        lean_dec(v_snd_3650_);
                        lean_dec(v_mvarId_3638_);
                        v_a_3728_ = lean_ctor_get(v___x_3708_, 0);
                        v_isSharedCheck_3735_ = (!lean_is_exclusive(v___x_3708_)) as u8;
                        if v_isSharedCheck_3735_ == 0 {
                            v___x_3730_ = v___x_3708_;
                            v_isShared_3731_ = v_isSharedCheck_3735_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_3728_);
                            lean_dec(v___x_3708_);
                            v___x_3730_ = lean_box(0);
                            v_isShared_3731_ = v_isSharedCheck_3735_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3702_);
                    lean_dec(v_val_3700_);
                    lean_dec_ref(v_negMap_3691_);
                    lean_dec(v_fst_3674_);
                    lean_del_object(v___x_3672_);
                    lean_dec(v_val_3670_);
                    lean_del_object(v___x_3652_);
                    lean_dec(v_snd_3650_);
                    lean_dec(v_mvarId_3638_);
                    v_a_3736_ = lean_ctor_get(v___x_3704_, 0);
                    v_isSharedCheck_3743_ = (!lean_is_exclusive(v___x_3704_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v___x_3738_ = v___x_3704_;
                        v_isShared_3739_ = v_isSharedCheck_3743_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3736_);
                        lean_dec(v___x_3704_);
                        v___x_3738_ = lean_box(0);
                        v_isShared_3739_ = v_isSharedCheck_3743_;
                        state = 17;
                        continue;
                    }
                }
            }
            11 => {
                v___x_3714_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3714_, 0, v_fst_3674_);
                lean_ctor_set(v___x_3714_, 1, v_negMap_3691_);
                v___x_3715_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3715_, 0, v___x_3713_);
                lean_ctor_set(v___x_3715_, 1, v___x_3714_);
                if v_isShared_3673_ == 0 {
                    lean_ctor_set_tag(v___x_3672_, 0);
                    lean_ctor_set(v___x_3672_, 0, v___x_3715_);
                    v___x_3717_ = v___x_3672_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3715_);
                    v___x_3717_ = v_reuseFailAlloc_3718_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v_a_3655_ = v___x_3717_;
                state = 2;
                continue;
            }
            13 => {
                if v_isShared_3723_ == 0 {
                    v___x_3725_ = v___x_3722_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
                    v___x_3725_ = v_reuseFailAlloc_3726_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3725_;
            }
            15 => {
                if v_isShared_3731_ == 0 {
                    v___x_3733_ = v___x_3730_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
                    v___x_3733_ = v_reuseFailAlloc_3734_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3733_;
            }
            17 => {
                if v_isShared_3739_ == 0 {
                    v___x_3741_ = v___x_3738_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
                    v___x_3741_ = v_reuseFailAlloc_3742_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3741_;
            }
            19 => {
                if v_isShared_3750_ == 0 {
                    v___x_3752_ = v___x_3749_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
                    v___x_3752_ = v_reuseFailAlloc_3753_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3752_;
            }
            21 => {
                v___x_3759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(v_fst_3674_, v_val_3755_);
                if lean_obj_tag(v___x_3759_) == 1 {
                    lean_dec(v_val_3755_);
                    lean_dec_ref(v___x_3687_);
                    lean_del_object(v___x_3677_);
                    lean_del_object(v___x_3672_);
                    v_val_3760_ = lean_ctor_get(v___x_3759_, 0);
                    v_isSharedCheck_3804_ = (!lean_is_exclusive(v___x_3759_)) as u8;
                    if v_isSharedCheck_3804_ == 0 {
                        v___x_3762_ = v___x_3759_;
                        v_isShared_3763_ = v_isSharedCheck_3804_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_val_3760_);
                        lean_dec(v___x_3759_);
                        v___x_3762_ = lean_box(0);
                        v_isShared_3763_ = v_isSharedCheck_3804_;
                        state = 22;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3759_);
                    lean_del_object(v___x_3757_);
                    v___x_3805_ = l_Lean_LocalDecl_fvarId(v_val_3670_);
                    v___x_3806_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2___redArg(v_snd_3675_, v_val_3755_, v___x_3805_);
                    v_negMap_3691_ = v___x_3806_;
                    v___y_3692_ = v___y_3643_;
                    v___y_3693_ = v___y_3644_;
                    v___y_3694_ = v___y_3645_;
                    v___y_3695_ = v___y_3646_;
                    state = 9;
                    continue;
                }
            }
            22 => {
                lean_inc(v_mvarId_3638_);
                v___x_3764_ = l_Lean_MVarId_getType(
                    v_mvarId_3638_,
                    v___y_3643_,
                    v___y_3644_,
                    v___y_3645_,
                    v___y_3646_,
                );
                if lean_obj_tag(v___x_3764_) == 0 {
                    v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
                    lean_inc(v_a_3765_);
                    lean_dec_ref_known(v___x_3764_, 1);
                    v___x_3766_ = l_Lean_mkFVar(v_val_3760_);
                    v___x_3767_ = l_Lean_LocalDecl_toExpr(v_val_3670_);
                    v___x_3768_ = l_Lean_Meta_mkAbsurd(
                        v_a_3765_,
                        v___x_3766_,
                        v___x_3767_,
                        v___y_3643_,
                        v___y_3644_,
                        v___y_3645_,
                        v___y_3646_,
                    );
                    if lean_obj_tag(v___x_3768_) == 0 {
                        v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
                        lean_inc(v_a_3769_);
                        lean_dec_ref_known(v___x_3768_, 1);
                        v___x_3770_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(v_mvarId_3638_, v_a_3769_, v___y_3644_);
                        if lean_obj_tag(v___x_3770_) == 0 {
                            lean_dec_ref_known(v___x_3770_, 1);
                            v___x_3771_ = lean_box((v___x_3648_) as usize);
                            if v_isShared_3763_ == 0 {
                                lean_ctor_set(v___x_3762_, 0, v___x_3771_);
                                v___x_3773_ = v___x_3762_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3771_);
                                v___x_3773_ = v_reuseFailAlloc_3779_;
                                state = 23;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3762_);
                            lean_del_object(v___x_3757_);
                            lean_dec(v_snd_3675_);
                            lean_dec(v_fst_3674_);
                            lean_del_object(v___x_3652_);
                            lean_dec(v_snd_3650_);
                            v_a_3780_ = lean_ctor_get(v___x_3770_, 0);
                            v_isSharedCheck_3787_ = (!lean_is_exclusive(v___x_3770_)) as u8;
                            if v_isSharedCheck_3787_ == 0 {
                                v___x_3782_ = v___x_3770_;
                                v_isShared_3783_ = v_isSharedCheck_3787_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_3780_);
                                lean_dec(v___x_3770_);
                                v___x_3782_ = lean_box(0);
                                v_isShared_3783_ = v_isSharedCheck_3787_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_3762_);
                        lean_del_object(v___x_3757_);
                        lean_dec(v_snd_3675_);
                        lean_dec(v_fst_3674_);
                        lean_del_object(v___x_3652_);
                        lean_dec(v_snd_3650_);
                        lean_dec(v_mvarId_3638_);
                        v_a_3788_ = lean_ctor_get(v___x_3768_, 0);
                        v_isSharedCheck_3795_ = (!lean_is_exclusive(v___x_3768_)) as u8;
                        if v_isSharedCheck_3795_ == 0 {
                            v___x_3790_ = v___x_3768_;
                            v_isShared_3791_ = v_isSharedCheck_3795_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_3788_);
                            lean_dec(v___x_3768_);
                            v___x_3790_ = lean_box(0);
                            v_isShared_3791_ = v_isSharedCheck_3795_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3762_);
                    lean_dec(v_val_3760_);
                    lean_del_object(v___x_3757_);
                    lean_dec(v_snd_3675_);
                    lean_dec(v_fst_3674_);
                    lean_dec(v_val_3670_);
                    lean_del_object(v___x_3652_);
                    lean_dec(v_snd_3650_);
                    lean_dec(v_mvarId_3638_);
                    v_a_3796_ = lean_ctor_get(v___x_3764_, 0);
                    v_isSharedCheck_3803_ = (!lean_is_exclusive(v___x_3764_)) as u8;
                    if v_isSharedCheck_3803_ == 0 {
                        v___x_3798_ = v___x_3764_;
                        v_isShared_3799_ = v_isSharedCheck_3803_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_a_3796_);
                        lean_dec(v___x_3764_);
                        v___x_3798_ = lean_box(0);
                        v_isShared_3799_ = v_isSharedCheck_3803_;
                        state = 29;
                        continue;
                    }
                }
            }
            23 => {
                v___x_3774_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3774_, 0, v_fst_3674_);
                lean_ctor_set(v___x_3774_, 1, v_snd_3675_);
                v___x_3775_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3775_, 0, v___x_3773_);
                lean_ctor_set(v___x_3775_, 1, v___x_3774_);
                if v_isShared_3758_ == 0 {
                    lean_ctor_set_tag(v___x_3757_, 0);
                    lean_ctor_set(v___x_3757_, 0, v___x_3775_);
                    v___x_3777_ = v___x_3757_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3775_);
                    v___x_3777_ = v_reuseFailAlloc_3778_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_a_3655_ = v___x_3777_;
                state = 2;
                continue;
            }
            25 => {
                if v_isShared_3783_ == 0 {
                    v___x_3785_ = v___x_3782_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
                    v___x_3785_ = v_reuseFailAlloc_3786_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3785_;
            }
            27 => {
                if v_isShared_3791_ == 0 {
                    v___x_3793_ = v___x_3790_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
                    v___x_3793_ = v_reuseFailAlloc_3794_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3793_;
            }
            29 => {
                if v_isShared_3799_ == 0 {
                    v___x_3801_ = v___x_3798_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
                    v___x_3801_ = v_reuseFailAlloc_3802_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3801_;
            }
            31 => {
                if v_isShared_3811_ == 0 {
                    v___x_3813_ = v___x_3810_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
                    v___x_3813_ = v_reuseFailAlloc_3814_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__13___boxed(
    mut v_mvarId_3820_: *mut LeanObject,
    mut v_as_3821_: *mut LeanObject,
    mut v_sz_3822_: *mut LeanObject,
    mut v_i_3823_: *mut LeanObject,
    mut v_b_3824_: *mut LeanObject,
    mut v___y_3825_: *mut LeanObject,
    mut v___y_3826_: *mut LeanObject,
    mut v___y_3827_: *mut LeanObject,
    mut v___y_3828_: *mut LeanObject,
    mut v___y_3829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3830_: usize = 0;
    let mut v_i_boxed_3831_: usize = 0;
    let mut v_res_3832_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3830_ = lean_unbox_usize(v_sz_3822_);
    lean_dec(v_sz_3822_);
    v_i_boxed_3831_ = lean_unbox_usize(v_i_3823_);
    lean_dec(v_i_3823_);
    v_res_3832_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__13(v_mvarId_3820_, v_as_3821_, v_sz_boxed_3830_, v_i_boxed_3831_, v_b_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
    lean_dec(v___y_3828_);
    lean_dec_ref(v___y_3827_);
    lean_dec(v___y_3826_);
    lean_dec_ref(v___y_3825_);
    lean_dec_ref(v_as_3821_);
    return v_res_3832_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8(
    mut v_init_3833_: *mut LeanObject,
    mut v_mvarId_3834_: *mut LeanObject,
    mut v_n_3835_: *mut LeanObject,
    mut v_b_3836_: *mut LeanObject,
    mut v___y_3837_: *mut LeanObject,
    mut v___y_3838_: *mut LeanObject,
    mut v___y_3839_: *mut LeanObject,
    mut v___y_3840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3845_: usize = 0;
    let mut v___x_3846_: usize = 0;
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v_fst_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3862_: u8 = 0;
    let mut v_a_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3866_: u8 = 0;
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3870_: u8 = 0;
    let mut v_vs_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3874_: usize = 0;
    let mut v___x_3875_: usize = 0;
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3880_: u8 = 0;
    let mut v_fst_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3891_: u8 = 0;
    let mut v_a_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3895_: u8 = 0;
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3899_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_3835_) == 0 {
                    v_cs_3842_ = lean_ctor_get(v_n_3835_, 0);
                    v___x_3843_ = lean_box(0);
                    v___x_3844_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3844_, 0, v___x_3843_);
                    lean_ctor_set(v___x_3844_, 1, v_b_3836_);
                    v_sz_3845_ = lean_array_size(v_cs_3842_);
                    v___x_3846_ = 0usize;
                    v___x_3847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__12(v_init_3833_, v_mvarId_3834_, v_cs_3842_, v_sz_3845_, v___x_3846_, v___x_3844_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
                    if lean_obj_tag(v___x_3847_) == 0 {
                        v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
                        v_isSharedCheck_3862_ = (!lean_is_exclusive(v___x_3847_)) as u8;
                        if v_isSharedCheck_3862_ == 0 {
                            v___x_3850_ = v___x_3847_;
                            v_isShared_3851_ = v_isSharedCheck_3862_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3848_);
                            lean_dec(v___x_3847_);
                            v___x_3850_ = lean_box(0);
                            v_isShared_3851_ = v_isSharedCheck_3862_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3863_ = lean_ctor_get(v___x_3847_, 0);
                        v_isSharedCheck_3870_ = (!lean_is_exclusive(v___x_3847_)) as u8;
                        if v_isSharedCheck_3870_ == 0 {
                            v___x_3865_ = v___x_3847_;
                            v_isShared_3866_ = v_isSharedCheck_3870_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3863_);
                            lean_dec(v___x_3847_);
                            v___x_3865_ = lean_box(0);
                            v_isShared_3866_ = v_isSharedCheck_3870_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3871_ = lean_ctor_get(v_n_3835_, 0);
                    v___x_3872_ = lean_box(0);
                    v___x_3873_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3873_, 0, v___x_3872_);
                    lean_ctor_set(v___x_3873_, 1, v_b_3836_);
                    v_sz_3874_ = lean_array_size(v_vs_3871_);
                    v___x_3875_ = 0usize;
                    v___x_3876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__13(v_mvarId_3834_, v_vs_3871_, v_sz_3874_, v___x_3875_, v___x_3873_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_);
                    if lean_obj_tag(v___x_3876_) == 0 {
                        v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
                        v_isSharedCheck_3891_ = (!lean_is_exclusive(v___x_3876_)) as u8;
                        if v_isSharedCheck_3891_ == 0 {
                            v___x_3879_ = v___x_3876_;
                            v_isShared_3880_ = v_isSharedCheck_3891_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3877_);
                            lean_dec(v___x_3876_);
                            v___x_3879_ = lean_box(0);
                            v_isShared_3880_ = v_isSharedCheck_3891_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3892_ = lean_ctor_get(v___x_3876_, 0);
                        v_isSharedCheck_3899_ = (!lean_is_exclusive(v___x_3876_)) as u8;
                        if v_isSharedCheck_3899_ == 0 {
                            v___x_3894_ = v___x_3876_;
                            v_isShared_3895_ = v_isSharedCheck_3899_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3892_);
                            lean_dec(v___x_3876_);
                            v___x_3894_ = lean_box(0);
                            v_isShared_3895_ = v_isSharedCheck_3899_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3852_ = lean_ctor_get(v_a_3848_, 0);
                if lean_obj_tag(v_fst_3852_) == 0 {
                    v_snd_3853_ = lean_ctor_get(v_a_3848_, 1);
                    lean_inc(v_snd_3853_);
                    lean_dec(v_a_3848_);
                    v___x_3854_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3854_, 0, v_snd_3853_);
                    if v_isShared_3851_ == 0 {
                        lean_ctor_set(v___x_3850_, 0, v___x_3854_);
                        v___x_3856_ = v___x_3850_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
                        v___x_3856_ = v_reuseFailAlloc_3857_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3852_);
                    lean_dec(v_a_3848_);
                    v_val_3858_ = lean_ctor_get(v_fst_3852_, 0);
                    lean_inc(v_val_3858_);
                    lean_dec_ref_known(v_fst_3852_, 1);
                    if v_isShared_3851_ == 0 {
                        lean_ctor_set(v___x_3850_, 0, v_val_3858_);
                        v___x_3860_ = v___x_3850_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_val_3858_);
                        v___x_3860_ = v_reuseFailAlloc_3861_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3856_;
            }
            3 => {
                return v___x_3860_;
            }
            4 => {
                if v_isShared_3866_ == 0 {
                    v___x_3868_ = v___x_3865_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
                    v___x_3868_ = v_reuseFailAlloc_3869_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3868_;
            }
            6 => {
                v_fst_3881_ = lean_ctor_get(v_a_3877_, 0);
                if lean_obj_tag(v_fst_3881_) == 0 {
                    v_snd_3882_ = lean_ctor_get(v_a_3877_, 1);
                    lean_inc(v_snd_3882_);
                    lean_dec(v_a_3877_);
                    v___x_3883_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3883_, 0, v_snd_3882_);
                    if v_isShared_3880_ == 0 {
                        lean_ctor_set(v___x_3879_, 0, v___x_3883_);
                        v___x_3885_ = v___x_3879_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
                        v___x_3885_ = v_reuseFailAlloc_3886_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3881_);
                    lean_dec(v_a_3877_);
                    v_val_3887_ = lean_ctor_get(v_fst_3881_, 0);
                    lean_inc(v_val_3887_);
                    lean_dec_ref_known(v_fst_3881_, 1);
                    if v_isShared_3880_ == 0 {
                        lean_ctor_set(v___x_3879_, 0, v_val_3887_);
                        v___x_3889_ = v___x_3879_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3890_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_val_3887_);
                        v___x_3889_ = v_reuseFailAlloc_3890_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3885_;
            }
            8 => {
                return v___x_3889_;
            }
            9 => {
                if v_isShared_3895_ == 0 {
                    v___x_3897_ = v___x_3894_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
                    v___x_3897_ = v_reuseFailAlloc_3898_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__12(
    mut v_init_3900_: *mut LeanObject,
    mut v_mvarId_3901_: *mut LeanObject,
    mut v_as_3902_: *mut LeanObject,
    mut v_sz_3903_: usize,
    mut v_i_3904_: usize,
    mut v_b_3905_: *mut LeanObject,
    mut v___y_3906_: *mut LeanObject,
    mut v___y_3907_: *mut LeanObject,
    mut v___y_3908_: *mut LeanObject,
    mut v___y_3909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3911_: u8 = 0;
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3916_: u8 = 0;
    let mut v_a_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: usize = 0;
    let mut v___x_3935_: usize = 0;
    let mut v_reuseFailAlloc_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3938_: u8 = 0;
    let mut v_a_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v_isSharedCheck_3947_: u8 = 0;
    let mut v_unused_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3911_ = lean_usize_dec_lt(v_i_3904_, v_sz_3903_);
                if v___x_3911_ == 0 {
                    lean_dec(v_mvarId_3901_);
                    v___x_3912_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3912_, 0, v_b_3905_);
                    return v___x_3912_;
                } else {
                    v_snd_3913_ = lean_ctor_get(v_b_3905_, 1);
                    v_isSharedCheck_3947_ = (!lean_is_exclusive(v_b_3905_)) as u8;
                    if v_isSharedCheck_3947_ == 0 {
                        v_unused_3948_ = lean_ctor_get(v_b_3905_, 0);
                        lean_dec(v_unused_3948_);
                        v___x_3915_ = v_b_3905_;
                        v_isShared_3916_ = v_isSharedCheck_3947_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3913_);
                        lean_dec(v_b_3905_);
                        v___x_3915_ = lean_box(0);
                        v_isShared_3916_ = v_isSharedCheck_3947_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3917_ = lean_array_uget_borrowed(v_as_3902_, v_i_3904_);
                lean_inc(v_snd_3913_);
                lean_inc(v_mvarId_3901_);
                v___x_3918_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8(v_init_3900_, v_mvarId_3901_, v_a_3917_, v_snd_3913_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
                if lean_obj_tag(v___x_3918_) == 0 {
                    v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
                    v_isSharedCheck_3938_ = (!lean_is_exclusive(v___x_3918_)) as u8;
                    if v_isSharedCheck_3938_ == 0 {
                        v___x_3921_ = v___x_3918_;
                        v_isShared_3922_ = v_isSharedCheck_3938_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3919_);
                        lean_dec(v___x_3918_);
                        v___x_3921_ = lean_box(0);
                        v_isShared_3922_ = v_isSharedCheck_3938_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3915_);
                    lean_dec(v_snd_3913_);
                    lean_dec(v_mvarId_3901_);
                    v_a_3939_ = lean_ctor_get(v___x_3918_, 0);
                    v_isSharedCheck_3946_ = (!lean_is_exclusive(v___x_3918_)) as u8;
                    if v_isSharedCheck_3946_ == 0 {
                        v___x_3941_ = v___x_3918_;
                        v_isShared_3942_ = v_isSharedCheck_3946_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3939_);
                        lean_dec(v___x_3918_);
                        v___x_3941_ = lean_box(0);
                        v_isShared_3942_ = v_isSharedCheck_3946_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_3919_) == 0 {
                    lean_dec(v_mvarId_3901_);
                    v___x_3923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3923_, 0, v_a_3919_);
                    if v_isShared_3916_ == 0 {
                        lean_ctor_set(v___x_3915_, 0, v___x_3923_);
                        v___x_3925_ = v___x_3915_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3923_);
                        lean_ctor_set(v_reuseFailAlloc_3929_, 1, v_snd_3913_);
                        v___x_3925_ = v_reuseFailAlloc_3929_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3921_);
                    lean_dec(v_snd_3913_);
                    v_a_3930_ = lean_ctor_get(v_a_3919_, 0);
                    lean_inc(v_a_3930_);
                    lean_dec_ref_known(v_a_3919_, 1);
                    v___x_3931_ = lean_box(0);
                    if v_isShared_3916_ == 0 {
                        lean_ctor_set(v___x_3915_, 1, v_a_3930_);
                        lean_ctor_set(v___x_3915_, 0, v___x_3931_);
                        v___x_3933_ = v___x_3915_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3931_);
                        lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_a_3930_);
                        v___x_3933_ = v_reuseFailAlloc_3937_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3922_ == 0 {
                    lean_ctor_set(v___x_3921_, 0, v___x_3925_);
                    v___x_3927_ = v___x_3921_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3925_);
                    v___x_3927_ = v_reuseFailAlloc_3928_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3927_;
            }
            5 => {
                v___x_3934_ = 1usize;
                v___x_3935_ = lean_usize_add(v_i_3904_, v___x_3934_);
                v_i_3904_ = v___x_3935_;
                v_b_3905_ = v___x_3933_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_3942_ == 0 {
                    v___x_3944_ = v___x_3941_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
                    v___x_3944_ = v_reuseFailAlloc_3945_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3944_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__12___boxed(
    mut v_init_3949_: *mut LeanObject,
    mut v_mvarId_3950_: *mut LeanObject,
    mut v_as_3951_: *mut LeanObject,
    mut v_sz_3952_: *mut LeanObject,
    mut v_i_3953_: *mut LeanObject,
    mut v_b_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
    mut v___y_3956_: *mut LeanObject,
    mut v___y_3957_: *mut LeanObject,
    mut v___y_3958_: *mut LeanObject,
    mut v___y_3959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3960_: usize = 0;
    let mut v_i_boxed_3961_: usize = 0;
    let mut v_res_3962_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3960_ = lean_unbox_usize(v_sz_3952_);
    lean_dec(v_sz_3952_);
    v_i_boxed_3961_ = lean_unbox_usize(v_i_3953_);
    lean_dec(v_i_3953_);
    v_res_3962_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8_spec__12(v_init_3949_, v_mvarId_3950_, v_as_3951_, v_sz_boxed_3960_, v_i_boxed_3961_, v_b_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
    lean_dec(v___y_3958_);
    lean_dec_ref(v___y_3957_);
    lean_dec(v___y_3956_);
    lean_dec_ref(v___y_3955_);
    lean_dec_ref(v_as_3951_);
    lean_dec_ref(v_init_3949_);
    return v_res_3962_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8___boxed(
    mut v_init_3963_: *mut LeanObject,
    mut v_mvarId_3964_: *mut LeanObject,
    mut v_n_3965_: *mut LeanObject,
    mut v_b_3966_: *mut LeanObject,
    mut v___y_3967_: *mut LeanObject,
    mut v___y_3968_: *mut LeanObject,
    mut v___y_3969_: *mut LeanObject,
    mut v___y_3970_: *mut LeanObject,
    mut v___y_3971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3972_: *mut LeanObject = core::ptr::null_mut();
    v_res_3972_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8(v_init_3963_, v_mvarId_3964_, v_n_3965_, v_b_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
    lean_dec(v___y_3970_);
    lean_dec_ref(v___y_3969_);
    lean_dec(v___y_3968_);
    lean_dec_ref(v___y_3967_);
    lean_dec_ref(v_n_3965_);
    lean_dec_ref(v_init_3963_);
    return v_res_3972_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__9_spec__15(
    mut v_mvarId_3973_: *mut LeanObject,
    mut v_as_3974_: *mut LeanObject,
    mut v_sz_3975_: usize,
    mut v_i_3976_: usize,
    mut v_b_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
    mut v___y_3980_: *mut LeanObject,
    mut v___y_3981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3983_: u8 = 0;
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3988_: u8 = 0;
    let mut v_a_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: usize = 0;
    let mut v___x_4001_: usize = 0;
    let mut v_a_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4010_: u8 = 0;
    let mut v_posMap_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negMap_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: u8 = 0;
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negMap_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: u8 = 0;
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4056_: u8 = 0;
    let mut v_a_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v_a_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4068_: u8 = 0;
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v_isSharedCheck_4073_: u8 = 0;
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4083_: u8 = 0;
    let mut v_val_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4089_: u8 = 0;
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4110_: u8 = 0;
    let mut v_a_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4114_: u8 = 0;
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4118_: u8 = 0;
    let mut v_a_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4122_: u8 = 0;
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4126_: u8 = 0;
    let mut v_isSharedCheck_4127_: u8 = 0;
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut v_isSharedCheck_4139_: u8 = 0;
    let mut v_unused_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3983_ = lean_usize_dec_lt(v_i_3976_, v_sz_3975_);
                if v___x_3983_ == 0 {
                    lean_dec(v_mvarId_3973_);
                    v___x_3984_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3984_, 0, v_b_3977_);
                    return v___x_3984_;
                } else {
                    v_snd_3985_ = lean_ctor_get(v_b_3977_, 1);
                    v_isSharedCheck_4139_ = (!lean_is_exclusive(v_b_3977_)) as u8;
                    if v_isSharedCheck_4139_ == 0 {
                        v_unused_4140_ = lean_ctor_get(v_b_3977_, 0);
                        lean_dec(v_unused_4140_);
                        v___x_3987_ = v_b_3977_;
                        v_isShared_3988_ = v_isSharedCheck_4139_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3985_);
                        lean_dec(v_b_3977_);
                        v___x_3987_ = lean_box(0);
                        v_isShared_3988_ = v_isSharedCheck_4139_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3996_ = lean_box(0);
                v_a_4003_ = lean_array_uget_borrowed(v_as_3974_, v_i_3976_);
                if lean_obj_tag(v_a_4003_) == 0 {
                    lean_del_object(v___x_3987_);
                    v_a_3998_ = v_snd_3985_;
                    state = 4;
                    continue;
                } else {
                    v_snd_4004_ = lean_ctor_get(v_snd_3985_, 1);
                    lean_inc(v_snd_4004_);
                    v_val_4005_ = lean_ctor_get(v_a_4003_, 0);
                    v_fst_4006_ = lean_ctor_get(v_snd_4004_, 0);
                    v_snd_4007_ = lean_ctor_get(v_snd_4004_, 1);
                    v_isSharedCheck_4138_ = (!lean_is_exclusive(v_snd_4004_)) as u8;
                    if v_isSharedCheck_4138_ == 0 {
                        v___x_4009_ = v_snd_4004_;
                        v_isShared_4010_ = v_isSharedCheck_4138_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_4007_);
                        lean_inc(v_fst_4006_);
                        lean_dec(v_snd_4004_);
                        v___x_4009_ = lean_box(0);
                        v_isShared_4010_ = v_isSharedCheck_4138_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3991_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3991_, 0, v_a_3990_);
                if v_isShared_3988_ == 0 {
                    lean_ctor_set(v___x_3987_, 0, v___x_3991_);
                    v___x_3993_ = v___x_3987_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3991_);
                    lean_ctor_set(v_reuseFailAlloc_3995_, 1, v_snd_3985_);
                    v___x_3993_ = v_reuseFailAlloc_3995_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3994_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3994_, 0, v___x_3993_);
                return v___x_3994_;
            }
            4 => {
                v___x_3999_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3999_, 0, v___x_3996_);
                lean_ctor_set(v___x_3999_, 1, v_a_3998_);
                v___x_4000_ = 1usize;
                v___x_4001_ = lean_usize_add(v_i_3976_, v___x_4000_);
                v_i_3976_ = v___x_4001_;
                v_b_3977_ = v___x_3999_;
                state = 0;
                continue;
            }
            5 => {
                v___x_4018_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4005_);
                if v___x_4018_ == 0 {
                    v___x_4019_ = l_Lean_LocalDecl_type(v_val_4005_);
                    lean_inc_ref(v___x_4019_);
                    v___x_4020_ = l_Lean_Meta_matchNot_x3f(
                        v___x_4019_,
                        v___y_3978_,
                        v___y_3979_,
                        v___y_3980_,
                        v___y_3981_,
                    );
                    if lean_obj_tag(v___x_4020_) == 0 {
                        v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
                        lean_inc(v_a_4021_);
                        lean_dec_ref_known(v___x_4020_, 1);
                        if lean_obj_tag(v_a_4021_) == 1 {
                            v_val_4084_ = lean_ctor_get(v_a_4021_, 0);
                            lean_inc(v_val_4084_);
                            lean_dec_ref_known(v_a_4021_, 1);
                            v___x_4085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(v_fst_4006_, v_val_4084_);
                            if lean_obj_tag(v___x_4085_) == 1 {
                                lean_dec(v_val_4084_);
                                lean_dec_ref(v___x_4019_);
                                lean_del_object(v___x_4009_);
                                v_val_4086_ = lean_ctor_get(v___x_4085_, 0);
                                v_isSharedCheck_4127_ = (!lean_is_exclusive(v___x_4085_)) as u8;
                                if v_isSharedCheck_4127_ == 0 {
                                    v___x_4088_ = v___x_4085_;
                                    v_isShared_4089_ = v_isSharedCheck_4127_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_val_4086_);
                                    lean_dec(v___x_4085_);
                                    v___x_4088_ = lean_box(0);
                                    v_isShared_4089_ = v_isSharedCheck_4127_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_4085_);
                                v___x_4128_ = l_Lean_LocalDecl_fvarId(v_val_4005_);
                                v___x_4129_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2___redArg(v_snd_4007_, v_val_4084_, v___x_4128_);
                                v_negMap_4023_ = v___x_4129_;
                                v___y_4024_ = v___y_3978_;
                                v___y_4025_ = v___y_3979_;
                                v___y_4026_ = v___y_3980_;
                                v___y_4027_ = v___y_3981_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4021_);
                            v_negMap_4023_ = v_snd_4007_;
                            v___y_4024_ = v___y_3978_;
                            v___y_4025_ = v___y_3979_;
                            v___y_4026_ = v___y_3980_;
                            v___y_4027_ = v___y_3981_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4019_);
                        lean_del_object(v___x_4009_);
                        lean_dec(v_snd_4007_);
                        lean_dec(v_fst_4006_);
                        lean_del_object(v___x_3987_);
                        lean_dec(v_snd_3985_);
                        lean_dec(v_mvarId_3973_);
                        v_a_4130_ = lean_ctor_get(v___x_4020_, 0);
                        v_isSharedCheck_4137_ = (!lean_is_exclusive(v___x_4020_)) as u8;
                        if v_isSharedCheck_4137_ == 0 {
                            v___x_4132_ = v___x_4020_;
                            v_isShared_4133_ = v_isSharedCheck_4137_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_4130_);
                            lean_dec(v___x_4020_);
                            v___x_4132_ = lean_box(0);
                            v_isShared_4133_ = v_isSharedCheck_4137_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3987_);
                    lean_dec(v_snd_3985_);
                    v_posMap_4012_ = v_fst_4006_;
                    v_negMap_4013_ = v_snd_4007_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4010_ == 0 {
                    lean_ctor_set(v___x_4009_, 1, v_negMap_4013_);
                    lean_ctor_set(v___x_4009_, 0, v_posMap_4012_);
                    v___x_4015_ = v___x_4009_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_posMap_4012_);
                    lean_ctor_set(v_reuseFailAlloc_4017_, 1, v_negMap_4013_);
                    v___x_4015_ = v_reuseFailAlloc_4017_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4016_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4016_, 0, v___x_3996_);
                lean_ctor_set(v___x_4016_, 1, v___x_4015_);
                v_a_3998_ = v___x_4016_;
                state = 4;
                continue;
            }
            8 => {
                lean_inc_ref(v___x_4019_);
                v___x_4028_ = l_Lean_Meta_isProp(
                    v___x_4019_,
                    v___y_4024_,
                    v___y_4025_,
                    v___y_4026_,
                    v___y_4027_,
                );
                if lean_obj_tag(v___x_4028_) == 0 {
                    v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
                    lean_inc(v_a_4029_);
                    lean_dec_ref_known(v___x_4028_, 1);
                    v___x_4030_ = (lean_unbox(v_a_4029_) as u8);
                    lean_dec(v_a_4029_);
                    if v___x_4030_ == 0 {
                        lean_dec_ref(v___x_4019_);
                        lean_del_object(v___x_3987_);
                        lean_dec(v_snd_3985_);
                        v_posMap_4012_ = v_fst_4006_;
                        v_negMap_4013_ = v_negMap_4023_;
                        state = 6;
                        continue;
                    } else {
                        v___x_4031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(v_negMap_4023_, v___x_4019_);
                        if lean_obj_tag(v___x_4031_) == 1 {
                            lean_dec_ref(v___x_4019_);
                            lean_del_object(v___x_4009_);
                            v_val_4032_ = lean_ctor_get(v___x_4031_, 0);
                            v_isSharedCheck_4073_ = (!lean_is_exclusive(v___x_4031_)) as u8;
                            if v_isSharedCheck_4073_ == 0 {
                                v___x_4034_ = v___x_4031_;
                                v_isShared_4035_ = v_isSharedCheck_4073_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_val_4032_);
                                lean_dec(v___x_4031_);
                                v___x_4034_ = lean_box(0);
                                v_isShared_4035_ = v_isSharedCheck_4073_;
                                state = 9;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_4031_);
                            lean_del_object(v___x_3987_);
                            lean_dec(v_snd_3985_);
                            v___x_4074_ = l_Lean_LocalDecl_fvarId(v_val_4005_);
                            v___x_4075_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2___redArg(v_fst_4006_, v___x_4019_, v___x_4074_);
                            v_posMap_4012_ = v___x_4075_;
                            v_negMap_4013_ = v_negMap_4023_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_negMap_4023_);
                    lean_dec_ref(v___x_4019_);
                    lean_del_object(v___x_4009_);
                    lean_dec(v_fst_4006_);
                    lean_del_object(v___x_3987_);
                    lean_dec(v_snd_3985_);
                    lean_dec(v_mvarId_3973_);
                    v_a_4076_ = lean_ctor_get(v___x_4028_, 0);
                    v_isSharedCheck_4083_ = (!lean_is_exclusive(v___x_4028_)) as u8;
                    if v_isSharedCheck_4083_ == 0 {
                        v___x_4078_ = v___x_4028_;
                        v_isShared_4079_ = v_isSharedCheck_4083_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_4076_);
                        lean_dec(v___x_4028_);
                        v___x_4078_ = lean_box(0);
                        v_isShared_4079_ = v_isSharedCheck_4083_;
                        state = 17;
                        continue;
                    }
                }
            }
            9 => {
                lean_inc(v_mvarId_3973_);
                v___x_4036_ = l_Lean_MVarId_getType(
                    v_mvarId_3973_,
                    v___y_4024_,
                    v___y_4025_,
                    v___y_4026_,
                    v___y_4027_,
                );
                if lean_obj_tag(v___x_4036_) == 0 {
                    v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
                    lean_inc(v_a_4037_);
                    lean_dec_ref_known(v___x_4036_, 1);
                    lean_inc(v_val_4005_);
                    v___x_4038_ = l_Lean_LocalDecl_toExpr(v_val_4005_);
                    v___x_4039_ = l_Lean_mkFVar(v_val_4032_);
                    v___x_4040_ = l_Lean_Meta_mkAbsurd(
                        v_a_4037_,
                        v___x_4038_,
                        v___x_4039_,
                        v___y_4024_,
                        v___y_4025_,
                        v___y_4026_,
                        v___y_4027_,
                    );
                    if lean_obj_tag(v___x_4040_) == 0 {
                        v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
                        lean_inc(v_a_4041_);
                        lean_dec_ref_known(v___x_4040_, 1);
                        v___x_4042_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(v_mvarId_3973_, v_a_4041_, v___y_4025_);
                        if lean_obj_tag(v___x_4042_) == 0 {
                            lean_dec_ref_known(v___x_4042_, 1);
                            v___x_4043_ = lean_box((v___x_3983_) as usize);
                            if v_isShared_4035_ == 0 {
                                lean_ctor_set(v___x_4034_, 0, v___x_4043_);
                                v___x_4045_ = v___x_4034_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4043_);
                                v___x_4045_ = v_reuseFailAlloc_4048_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4034_);
                            lean_dec_ref(v_negMap_4023_);
                            lean_dec(v_fst_4006_);
                            lean_del_object(v___x_3987_);
                            lean_dec(v_snd_3985_);
                            v_a_4049_ = lean_ctor_get(v___x_4042_, 0);
                            v_isSharedCheck_4056_ = (!lean_is_exclusive(v___x_4042_)) as u8;
                            if v_isSharedCheck_4056_ == 0 {
                                v___x_4051_ = v___x_4042_;
                                v_isShared_4052_ = v_isSharedCheck_4056_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_4049_);
                                lean_dec(v___x_4042_);
                                v___x_4051_ = lean_box(0);
                                v_isShared_4052_ = v_isSharedCheck_4056_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4034_);
                        lean_dec_ref(v_negMap_4023_);
                        lean_dec(v_fst_4006_);
                        lean_del_object(v___x_3987_);
                        lean_dec(v_snd_3985_);
                        lean_dec(v_mvarId_3973_);
                        v_a_4057_ = lean_ctor_get(v___x_4040_, 0);
                        v_isSharedCheck_4064_ = (!lean_is_exclusive(v___x_4040_)) as u8;
                        if v_isSharedCheck_4064_ == 0 {
                            v___x_4059_ = v___x_4040_;
                            v_isShared_4060_ = v_isSharedCheck_4064_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4057_);
                            lean_dec(v___x_4040_);
                            v___x_4059_ = lean_box(0);
                            v_isShared_4060_ = v_isSharedCheck_4064_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4034_);
                    lean_dec(v_val_4032_);
                    lean_dec_ref(v_negMap_4023_);
                    lean_dec(v_fst_4006_);
                    lean_del_object(v___x_3987_);
                    lean_dec(v_snd_3985_);
                    lean_dec(v_mvarId_3973_);
                    v_a_4065_ = lean_ctor_get(v___x_4036_, 0);
                    v_isSharedCheck_4072_ = (!lean_is_exclusive(v___x_4036_)) as u8;
                    if v_isSharedCheck_4072_ == 0 {
                        v___x_4067_ = v___x_4036_;
                        v_isShared_4068_ = v_isSharedCheck_4072_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4065_);
                        lean_dec(v___x_4036_);
                        v___x_4067_ = lean_box(0);
                        v_isShared_4068_ = v_isSharedCheck_4072_;
                        state = 15;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4046_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4046_, 0, v_fst_4006_);
                lean_ctor_set(v___x_4046_, 1, v_negMap_4023_);
                v___x_4047_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4047_, 0, v___x_4045_);
                lean_ctor_set(v___x_4047_, 1, v___x_4046_);
                v_a_3990_ = v___x_4047_;
                state = 2;
                continue;
            }
            11 => {
                if v_isShared_4052_ == 0 {
                    v___x_4054_ = v___x_4051_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
                    v___x_4054_ = v_reuseFailAlloc_4055_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4054_;
            }
            13 => {
                if v_isShared_4060_ == 0 {
                    v___x_4062_ = v___x_4059_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
                    v___x_4062_ = v_reuseFailAlloc_4063_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4062_;
            }
            15 => {
                if v_isShared_4068_ == 0 {
                    v___x_4070_ = v___x_4067_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
                    v___x_4070_ = v_reuseFailAlloc_4071_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4070_;
            }
            17 => {
                if v_isShared_4079_ == 0 {
                    v___x_4081_ = v___x_4078_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
                    v___x_4081_ = v_reuseFailAlloc_4082_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4081_;
            }
            19 => {
                lean_inc(v_mvarId_3973_);
                v___x_4090_ = l_Lean_MVarId_getType(
                    v_mvarId_3973_,
                    v___y_3978_,
                    v___y_3979_,
                    v___y_3980_,
                    v___y_3981_,
                );
                if lean_obj_tag(v___x_4090_) == 0 {
                    v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
                    lean_inc(v_a_4091_);
                    lean_dec_ref_known(v___x_4090_, 1);
                    v___x_4092_ = l_Lean_mkFVar(v_val_4086_);
                    lean_inc(v_val_4005_);
                    v___x_4093_ = l_Lean_LocalDecl_toExpr(v_val_4005_);
                    v___x_4094_ = l_Lean_Meta_mkAbsurd(
                        v_a_4091_,
                        v___x_4092_,
                        v___x_4093_,
                        v___y_3978_,
                        v___y_3979_,
                        v___y_3980_,
                        v___y_3981_,
                    );
                    if lean_obj_tag(v___x_4094_) == 0 {
                        v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
                        lean_inc(v_a_4095_);
                        lean_dec_ref_known(v___x_4094_, 1);
                        v___x_4096_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(v_mvarId_3973_, v_a_4095_, v___y_3979_);
                        if lean_obj_tag(v___x_4096_) == 0 {
                            lean_dec_ref_known(v___x_4096_, 1);
                            v___x_4097_ = lean_box((v___x_3983_) as usize);
                            if v_isShared_4089_ == 0 {
                                lean_ctor_set(v___x_4088_, 0, v___x_4097_);
                                v___x_4099_ = v___x_4088_;
                                state = 20;
                                continue;
                            } else {
                                v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4097_);
                                v___x_4099_ = v_reuseFailAlloc_4102_;
                                state = 20;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4088_);
                            lean_dec(v_snd_4007_);
                            lean_dec(v_fst_4006_);
                            lean_del_object(v___x_3987_);
                            lean_dec(v_snd_3985_);
                            v_a_4103_ = lean_ctor_get(v___x_4096_, 0);
                            v_isSharedCheck_4110_ = (!lean_is_exclusive(v___x_4096_)) as u8;
                            if v_isSharedCheck_4110_ == 0 {
                                v___x_4105_ = v___x_4096_;
                                v_isShared_4106_ = v_isSharedCheck_4110_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_4103_);
                                lean_dec(v___x_4096_);
                                v___x_4105_ = lean_box(0);
                                v_isShared_4106_ = v_isSharedCheck_4110_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4088_);
                        lean_dec(v_snd_4007_);
                        lean_dec(v_fst_4006_);
                        lean_del_object(v___x_3987_);
                        lean_dec(v_snd_3985_);
                        lean_dec(v_mvarId_3973_);
                        v_a_4111_ = lean_ctor_get(v___x_4094_, 0);
                        v_isSharedCheck_4118_ = (!lean_is_exclusive(v___x_4094_)) as u8;
                        if v_isSharedCheck_4118_ == 0 {
                            v___x_4113_ = v___x_4094_;
                            v_isShared_4114_ = v_isSharedCheck_4118_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_4111_);
                            lean_dec(v___x_4094_);
                            v___x_4113_ = lean_box(0);
                            v_isShared_4114_ = v_isSharedCheck_4118_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4088_);
                    lean_dec(v_val_4086_);
                    lean_dec(v_snd_4007_);
                    lean_dec(v_fst_4006_);
                    lean_del_object(v___x_3987_);
                    lean_dec(v_snd_3985_);
                    lean_dec(v_mvarId_3973_);
                    v_a_4119_ = lean_ctor_get(v___x_4090_, 0);
                    v_isSharedCheck_4126_ = (!lean_is_exclusive(v___x_4090_)) as u8;
                    if v_isSharedCheck_4126_ == 0 {
                        v___x_4121_ = v___x_4090_;
                        v_isShared_4122_ = v_isSharedCheck_4126_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_4119_);
                        lean_dec(v___x_4090_);
                        v___x_4121_ = lean_box(0);
                        v_isShared_4122_ = v_isSharedCheck_4126_;
                        state = 25;
                        continue;
                    }
                }
            }
            20 => {
                v___x_4100_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4100_, 0, v_fst_4006_);
                lean_ctor_set(v___x_4100_, 1, v_snd_4007_);
                v___x_4101_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4101_, 0, v___x_4099_);
                lean_ctor_set(v___x_4101_, 1, v___x_4100_);
                v_a_3990_ = v___x_4101_;
                state = 2;
                continue;
            }
            21 => {
                if v_isShared_4106_ == 0 {
                    v___x_4108_ = v___x_4105_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
                    v___x_4108_ = v_reuseFailAlloc_4109_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4108_;
            }
            23 => {
                if v_isShared_4114_ == 0 {
                    v___x_4116_ = v___x_4113_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
                    v___x_4116_ = v_reuseFailAlloc_4117_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4116_;
            }
            25 => {
                if v_isShared_4122_ == 0 {
                    v___x_4124_ = v___x_4121_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
                    v___x_4124_ = v_reuseFailAlloc_4125_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4124_;
            }
            27 => {
                if v_isShared_4133_ == 0 {
                    v___x_4135_ = v___x_4132_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
                    v___x_4135_ = v_reuseFailAlloc_4136_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__9_spec__15___boxed(
    mut v_mvarId_4141_: *mut LeanObject,
    mut v_as_4142_: *mut LeanObject,
    mut v_sz_4143_: *mut LeanObject,
    mut v_i_4144_: *mut LeanObject,
    mut v_b_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
    mut v___y_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4151_: usize = 0;
    let mut v_i_boxed_4152_: usize = 0;
    let mut v_res_4153_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4151_ = lean_unbox_usize(v_sz_4143_);
    lean_dec(v_sz_4143_);
    v_i_boxed_4152_ = lean_unbox_usize(v_i_4144_);
    lean_dec(v_i_4144_);
    v_res_4153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__9_spec__15(v_mvarId_4141_, v_as_4142_, v_sz_boxed_4151_, v_i_boxed_4152_, v_b_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
    lean_dec(v___y_4149_);
    lean_dec_ref(v___y_4148_);
    lean_dec(v___y_4147_);
    lean_dec_ref(v___y_4146_);
    lean_dec_ref(v_as_4142_);
    return v_res_4153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__9(
    mut v_mvarId_4154_: *mut LeanObject,
    mut v_as_4155_: *mut LeanObject,
    mut v_sz_4156_: usize,
    mut v_i_4157_: usize,
    mut v_b_4158_: *mut LeanObject,
    mut v___y_4159_: *mut LeanObject,
    mut v___y_4160_: *mut LeanObject,
    mut v___y_4161_: *mut LeanObject,
    mut v___y_4162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4164_: u8 = 0;
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v_a_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: usize = 0;
    let mut v___x_4182_: usize = 0;
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4191_: u8 = 0;
    let mut v_posMap_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negMap_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: u8 = 0;
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negMap_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: u8 = 0;
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4233_: u8 = 0;
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4237_: u8 = 0;
    let mut v_a_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4241_: u8 = 0;
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4245_: u8 = 0;
    let mut v_a_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4249_: u8 = 0;
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4253_: u8 = 0;
    let mut v_isSharedCheck_4254_: u8 = 0;
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4260_: u8 = 0;
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4264_: u8 = 0;
    let mut v_val_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4270_: u8 = 0;
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut v_a_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4299_: u8 = 0;
    let mut v_a_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4303_: u8 = 0;
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4307_: u8 = 0;
    let mut v_isSharedCheck_4308_: u8 = 0;
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4314_: u8 = 0;
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4318_: u8 = 0;
    let mut v_isSharedCheck_4319_: u8 = 0;
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_unused_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4164_ = lean_usize_dec_lt(v_i_4157_, v_sz_4156_);
                if v___x_4164_ == 0 {
                    lean_dec(v_mvarId_4154_);
                    v___x_4165_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4165_, 0, v_b_4158_);
                    return v___x_4165_;
                } else {
                    v_snd_4166_ = lean_ctor_get(v_b_4158_, 1);
                    v_isSharedCheck_4320_ = (!lean_is_exclusive(v_b_4158_)) as u8;
                    if v_isSharedCheck_4320_ == 0 {
                        v_unused_4321_ = lean_ctor_get(v_b_4158_, 0);
                        lean_dec(v_unused_4321_);
                        v___x_4168_ = v_b_4158_;
                        v_isShared_4169_ = v_isSharedCheck_4320_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4166_);
                        lean_dec(v_b_4158_);
                        v___x_4168_ = lean_box(0);
                        v_isShared_4169_ = v_isSharedCheck_4320_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4177_ = lean_box(0);
                v_a_4184_ = lean_array_uget_borrowed(v_as_4155_, v_i_4157_);
                if lean_obj_tag(v_a_4184_) == 0 {
                    lean_del_object(v___x_4168_);
                    v_a_4179_ = v_snd_4166_;
                    state = 4;
                    continue;
                } else {
                    v_snd_4185_ = lean_ctor_get(v_snd_4166_, 1);
                    lean_inc(v_snd_4185_);
                    v_val_4186_ = lean_ctor_get(v_a_4184_, 0);
                    v_fst_4187_ = lean_ctor_get(v_snd_4185_, 0);
                    v_snd_4188_ = lean_ctor_get(v_snd_4185_, 1);
                    v_isSharedCheck_4319_ = (!lean_is_exclusive(v_snd_4185_)) as u8;
                    if v_isSharedCheck_4319_ == 0 {
                        v___x_4190_ = v_snd_4185_;
                        v_isShared_4191_ = v_isSharedCheck_4319_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_4188_);
                        lean_inc(v_fst_4187_);
                        lean_dec(v_snd_4185_);
                        v___x_4190_ = lean_box(0);
                        v_isShared_4191_ = v_isSharedCheck_4319_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4172_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4172_, 0, v_a_4171_);
                if v_isShared_4169_ == 0 {
                    lean_ctor_set(v___x_4168_, 0, v___x_4172_);
                    v___x_4174_ = v___x_4168_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4172_);
                    lean_ctor_set(v_reuseFailAlloc_4176_, 1, v_snd_4166_);
                    v___x_4174_ = v_reuseFailAlloc_4176_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4175_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4175_, 0, v___x_4174_);
                return v___x_4175_;
            }
            4 => {
                v___x_4180_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4180_, 0, v___x_4177_);
                lean_ctor_set(v___x_4180_, 1, v_a_4179_);
                v___x_4181_ = 1usize;
                v___x_4182_ = lean_usize_add(v_i_4157_, v___x_4181_);
                v___x_4183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__9_spec__15(v_mvarId_4154_, v_as_4155_, v_sz_4156_, v___x_4182_, v___x_4180_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
                return v___x_4183_;
            }
            5 => {
                v___x_4199_ = l_Lean_LocalDecl_isImplementationDetail(v_val_4186_);
                if v___x_4199_ == 0 {
                    v___x_4200_ = l_Lean_LocalDecl_type(v_val_4186_);
                    lean_inc_ref(v___x_4200_);
                    v___x_4201_ = l_Lean_Meta_matchNot_x3f(
                        v___x_4200_,
                        v___y_4159_,
                        v___y_4160_,
                        v___y_4161_,
                        v___y_4162_,
                    );
                    if lean_obj_tag(v___x_4201_) == 0 {
                        v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
                        lean_inc(v_a_4202_);
                        lean_dec_ref_known(v___x_4201_, 1);
                        if lean_obj_tag(v_a_4202_) == 1 {
                            v_val_4265_ = lean_ctor_get(v_a_4202_, 0);
                            lean_inc(v_val_4265_);
                            lean_dec_ref_known(v_a_4202_, 1);
                            v___x_4266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(v_fst_4187_, v_val_4265_);
                            if lean_obj_tag(v___x_4266_) == 1 {
                                lean_dec(v_val_4265_);
                                lean_dec_ref(v___x_4200_);
                                lean_del_object(v___x_4190_);
                                v_val_4267_ = lean_ctor_get(v___x_4266_, 0);
                                v_isSharedCheck_4308_ = (!lean_is_exclusive(v___x_4266_)) as u8;
                                if v_isSharedCheck_4308_ == 0 {
                                    v___x_4269_ = v___x_4266_;
                                    v_isShared_4270_ = v_isSharedCheck_4308_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_val_4267_);
                                    lean_dec(v___x_4266_);
                                    v___x_4269_ = lean_box(0);
                                    v_isShared_4270_ = v_isSharedCheck_4308_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_4266_);
                                v___x_4309_ = l_Lean_LocalDecl_fvarId(v_val_4186_);
                                v___x_4310_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2___redArg(v_snd_4188_, v_val_4265_, v___x_4309_);
                                v_negMap_4204_ = v___x_4310_;
                                v___y_4205_ = v___y_4159_;
                                v___y_4206_ = v___y_4160_;
                                v___y_4207_ = v___y_4161_;
                                v___y_4208_ = v___y_4162_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4202_);
                            v_negMap_4204_ = v_snd_4188_;
                            v___y_4205_ = v___y_4159_;
                            v___y_4206_ = v___y_4160_;
                            v___y_4207_ = v___y_4161_;
                            v___y_4208_ = v___y_4162_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4200_);
                        lean_del_object(v___x_4190_);
                        lean_dec(v_snd_4188_);
                        lean_dec(v_fst_4187_);
                        lean_del_object(v___x_4168_);
                        lean_dec(v_snd_4166_);
                        lean_dec(v_mvarId_4154_);
                        v_a_4311_ = lean_ctor_get(v___x_4201_, 0);
                        v_isSharedCheck_4318_ = (!lean_is_exclusive(v___x_4201_)) as u8;
                        if v_isSharedCheck_4318_ == 0 {
                            v___x_4313_ = v___x_4201_;
                            v_isShared_4314_ = v_isSharedCheck_4318_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_4311_);
                            lean_dec(v___x_4201_);
                            v___x_4313_ = lean_box(0);
                            v_isShared_4314_ = v_isSharedCheck_4318_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4168_);
                    lean_dec(v_snd_4166_);
                    v_posMap_4193_ = v_fst_4187_;
                    v_negMap_4194_ = v_snd_4188_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4191_ == 0 {
                    lean_ctor_set(v___x_4190_, 1, v_negMap_4194_);
                    lean_ctor_set(v___x_4190_, 0, v_posMap_4193_);
                    v___x_4196_ = v___x_4190_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_posMap_4193_);
                    lean_ctor_set(v_reuseFailAlloc_4198_, 1, v_negMap_4194_);
                    v___x_4196_ = v_reuseFailAlloc_4198_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4197_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4197_, 0, v___x_4177_);
                lean_ctor_set(v___x_4197_, 1, v___x_4196_);
                v_a_4179_ = v___x_4197_;
                state = 4;
                continue;
            }
            8 => {
                lean_inc_ref(v___x_4200_);
                v___x_4209_ = l_Lean_Meta_isProp(
                    v___x_4200_,
                    v___y_4205_,
                    v___y_4206_,
                    v___y_4207_,
                    v___y_4208_,
                );
                if lean_obj_tag(v___x_4209_) == 0 {
                    v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
                    lean_inc(v_a_4210_);
                    lean_dec_ref_known(v___x_4209_, 1);
                    v___x_4211_ = (lean_unbox(v_a_4210_) as u8);
                    lean_dec(v_a_4210_);
                    if v___x_4211_ == 0 {
                        lean_dec_ref(v___x_4200_);
                        lean_del_object(v___x_4168_);
                        lean_dec(v_snd_4166_);
                        v_posMap_4193_ = v_fst_4187_;
                        v_negMap_4194_ = v_negMap_4204_;
                        state = 6;
                        continue;
                    } else {
                        v___x_4212_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(v_negMap_4204_, v___x_4200_);
                        if lean_obj_tag(v___x_4212_) == 1 {
                            lean_dec_ref(v___x_4200_);
                            lean_del_object(v___x_4190_);
                            v_val_4213_ = lean_ctor_get(v___x_4212_, 0);
                            v_isSharedCheck_4254_ = (!lean_is_exclusive(v___x_4212_)) as u8;
                            if v_isSharedCheck_4254_ == 0 {
                                v___x_4215_ = v___x_4212_;
                                v_isShared_4216_ = v_isSharedCheck_4254_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_val_4213_);
                                lean_dec(v___x_4212_);
                                v___x_4215_ = lean_box(0);
                                v_isShared_4216_ = v_isSharedCheck_4254_;
                                state = 9;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_4212_);
                            lean_del_object(v___x_4168_);
                            lean_dec(v_snd_4166_);
                            v___x_4255_ = l_Lean_LocalDecl_fvarId(v_val_4186_);
                            v___x_4256_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2___redArg(v_fst_4187_, v___x_4200_, v___x_4255_);
                            v_posMap_4193_ = v___x_4256_;
                            v_negMap_4194_ = v_negMap_4204_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_negMap_4204_);
                    lean_dec_ref(v___x_4200_);
                    lean_del_object(v___x_4190_);
                    lean_dec(v_fst_4187_);
                    lean_del_object(v___x_4168_);
                    lean_dec(v_snd_4166_);
                    lean_dec(v_mvarId_4154_);
                    v_a_4257_ = lean_ctor_get(v___x_4209_, 0);
                    v_isSharedCheck_4264_ = (!lean_is_exclusive(v___x_4209_)) as u8;
                    if v_isSharedCheck_4264_ == 0 {
                        v___x_4259_ = v___x_4209_;
                        v_isShared_4260_ = v_isSharedCheck_4264_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_4257_);
                        lean_dec(v___x_4209_);
                        v___x_4259_ = lean_box(0);
                        v_isShared_4260_ = v_isSharedCheck_4264_;
                        state = 17;
                        continue;
                    }
                }
            }
            9 => {
                lean_inc(v_mvarId_4154_);
                v___x_4217_ = l_Lean_MVarId_getType(
                    v_mvarId_4154_,
                    v___y_4205_,
                    v___y_4206_,
                    v___y_4207_,
                    v___y_4208_,
                );
                if lean_obj_tag(v___x_4217_) == 0 {
                    v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
                    lean_inc(v_a_4218_);
                    lean_dec_ref_known(v___x_4217_, 1);
                    lean_inc(v_val_4186_);
                    v___x_4219_ = l_Lean_LocalDecl_toExpr(v_val_4186_);
                    v___x_4220_ = l_Lean_mkFVar(v_val_4213_);
                    v___x_4221_ = l_Lean_Meta_mkAbsurd(
                        v_a_4218_,
                        v___x_4219_,
                        v___x_4220_,
                        v___y_4205_,
                        v___y_4206_,
                        v___y_4207_,
                        v___y_4208_,
                    );
                    if lean_obj_tag(v___x_4221_) == 0 {
                        v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
                        lean_inc(v_a_4222_);
                        lean_dec_ref_known(v___x_4221_, 1);
                        v___x_4223_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(v_mvarId_4154_, v_a_4222_, v___y_4206_);
                        if lean_obj_tag(v___x_4223_) == 0 {
                            lean_dec_ref_known(v___x_4223_, 1);
                            v___x_4224_ = lean_box((v___x_4164_) as usize);
                            if v_isShared_4216_ == 0 {
                                lean_ctor_set(v___x_4215_, 0, v___x_4224_);
                                v___x_4226_ = v___x_4215_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4224_);
                                v___x_4226_ = v_reuseFailAlloc_4229_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4215_);
                            lean_dec_ref(v_negMap_4204_);
                            lean_dec(v_fst_4187_);
                            lean_del_object(v___x_4168_);
                            lean_dec(v_snd_4166_);
                            v_a_4230_ = lean_ctor_get(v___x_4223_, 0);
                            v_isSharedCheck_4237_ = (!lean_is_exclusive(v___x_4223_)) as u8;
                            if v_isSharedCheck_4237_ == 0 {
                                v___x_4232_ = v___x_4223_;
                                v_isShared_4233_ = v_isSharedCheck_4237_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_4230_);
                                lean_dec(v___x_4223_);
                                v___x_4232_ = lean_box(0);
                                v_isShared_4233_ = v_isSharedCheck_4237_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4215_);
                        lean_dec_ref(v_negMap_4204_);
                        lean_dec(v_fst_4187_);
                        lean_del_object(v___x_4168_);
                        lean_dec(v_snd_4166_);
                        lean_dec(v_mvarId_4154_);
                        v_a_4238_ = lean_ctor_get(v___x_4221_, 0);
                        v_isSharedCheck_4245_ = (!lean_is_exclusive(v___x_4221_)) as u8;
                        if v_isSharedCheck_4245_ == 0 {
                            v___x_4240_ = v___x_4221_;
                            v_isShared_4241_ = v_isSharedCheck_4245_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4238_);
                            lean_dec(v___x_4221_);
                            v___x_4240_ = lean_box(0);
                            v_isShared_4241_ = v_isSharedCheck_4245_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4215_);
                    lean_dec(v_val_4213_);
                    lean_dec_ref(v_negMap_4204_);
                    lean_dec(v_fst_4187_);
                    lean_del_object(v___x_4168_);
                    lean_dec(v_snd_4166_);
                    lean_dec(v_mvarId_4154_);
                    v_a_4246_ = lean_ctor_get(v___x_4217_, 0);
                    v_isSharedCheck_4253_ = (!lean_is_exclusive(v___x_4217_)) as u8;
                    if v_isSharedCheck_4253_ == 0 {
                        v___x_4248_ = v___x_4217_;
                        v_isShared_4249_ = v_isSharedCheck_4253_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4246_);
                        lean_dec(v___x_4217_);
                        v___x_4248_ = lean_box(0);
                        v_isShared_4249_ = v_isSharedCheck_4253_;
                        state = 15;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4227_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4227_, 0, v_fst_4187_);
                lean_ctor_set(v___x_4227_, 1, v_negMap_4204_);
                v___x_4228_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4228_, 0, v___x_4226_);
                lean_ctor_set(v___x_4228_, 1, v___x_4227_);
                v_a_4171_ = v___x_4228_;
                state = 2;
                continue;
            }
            11 => {
                if v_isShared_4233_ == 0 {
                    v___x_4235_ = v___x_4232_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
                    v___x_4235_ = v_reuseFailAlloc_4236_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4235_;
            }
            13 => {
                if v_isShared_4241_ == 0 {
                    v___x_4243_ = v___x_4240_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
                    v___x_4243_ = v_reuseFailAlloc_4244_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4243_;
            }
            15 => {
                if v_isShared_4249_ == 0 {
                    v___x_4251_ = v___x_4248_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
                    v___x_4251_ = v_reuseFailAlloc_4252_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4251_;
            }
            17 => {
                if v_isShared_4260_ == 0 {
                    v___x_4262_ = v___x_4259_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
                    v___x_4262_ = v_reuseFailAlloc_4263_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4262_;
            }
            19 => {
                lean_inc(v_mvarId_4154_);
                v___x_4271_ = l_Lean_MVarId_getType(
                    v_mvarId_4154_,
                    v___y_4159_,
                    v___y_4160_,
                    v___y_4161_,
                    v___y_4162_,
                );
                if lean_obj_tag(v___x_4271_) == 0 {
                    v_a_4272_ = lean_ctor_get(v___x_4271_, 0);
                    lean_inc(v_a_4272_);
                    lean_dec_ref_known(v___x_4271_, 1);
                    v___x_4273_ = l_Lean_mkFVar(v_val_4267_);
                    lean_inc(v_val_4186_);
                    v___x_4274_ = l_Lean_LocalDecl_toExpr(v_val_4186_);
                    v___x_4275_ = l_Lean_Meta_mkAbsurd(
                        v_a_4272_,
                        v___x_4273_,
                        v___x_4274_,
                        v___y_4159_,
                        v___y_4160_,
                        v___y_4161_,
                        v___y_4162_,
                    );
                    if lean_obj_tag(v___x_4275_) == 0 {
                        v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
                        lean_inc(v_a_4276_);
                        lean_dec_ref_known(v___x_4275_, 1);
                        v___x_4277_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(v_mvarId_4154_, v_a_4276_, v___y_4160_);
                        if lean_obj_tag(v___x_4277_) == 0 {
                            lean_dec_ref_known(v___x_4277_, 1);
                            v___x_4278_ = lean_box((v___x_4164_) as usize);
                            if v_isShared_4270_ == 0 {
                                lean_ctor_set(v___x_4269_, 0, v___x_4278_);
                                v___x_4280_ = v___x_4269_;
                                state = 20;
                                continue;
                            } else {
                                v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4278_);
                                v___x_4280_ = v_reuseFailAlloc_4283_;
                                state = 20;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4269_);
                            lean_dec(v_snd_4188_);
                            lean_dec(v_fst_4187_);
                            lean_del_object(v___x_4168_);
                            lean_dec(v_snd_4166_);
                            v_a_4284_ = lean_ctor_get(v___x_4277_, 0);
                            v_isSharedCheck_4291_ = (!lean_is_exclusive(v___x_4277_)) as u8;
                            if v_isSharedCheck_4291_ == 0 {
                                v___x_4286_ = v___x_4277_;
                                v_isShared_4287_ = v_isSharedCheck_4291_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_4284_);
                                lean_dec(v___x_4277_);
                                v___x_4286_ = lean_box(0);
                                v_isShared_4287_ = v_isSharedCheck_4291_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4269_);
                        lean_dec(v_snd_4188_);
                        lean_dec(v_fst_4187_);
                        lean_del_object(v___x_4168_);
                        lean_dec(v_snd_4166_);
                        lean_dec(v_mvarId_4154_);
                        v_a_4292_ = lean_ctor_get(v___x_4275_, 0);
                        v_isSharedCheck_4299_ = (!lean_is_exclusive(v___x_4275_)) as u8;
                        if v_isSharedCheck_4299_ == 0 {
                            v___x_4294_ = v___x_4275_;
                            v_isShared_4295_ = v_isSharedCheck_4299_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_4292_);
                            lean_dec(v___x_4275_);
                            v___x_4294_ = lean_box(0);
                            v_isShared_4295_ = v_isSharedCheck_4299_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4269_);
                    lean_dec(v_val_4267_);
                    lean_dec(v_snd_4188_);
                    lean_dec(v_fst_4187_);
                    lean_del_object(v___x_4168_);
                    lean_dec(v_snd_4166_);
                    lean_dec(v_mvarId_4154_);
                    v_a_4300_ = lean_ctor_get(v___x_4271_, 0);
                    v_isSharedCheck_4307_ = (!lean_is_exclusive(v___x_4271_)) as u8;
                    if v_isSharedCheck_4307_ == 0 {
                        v___x_4302_ = v___x_4271_;
                        v_isShared_4303_ = v_isSharedCheck_4307_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_4300_);
                        lean_dec(v___x_4271_);
                        v___x_4302_ = lean_box(0);
                        v_isShared_4303_ = v_isSharedCheck_4307_;
                        state = 25;
                        continue;
                    }
                }
            }
            20 => {
                v___x_4281_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4281_, 0, v_fst_4187_);
                lean_ctor_set(v___x_4281_, 1, v_snd_4188_);
                v___x_4282_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4282_, 0, v___x_4280_);
                lean_ctor_set(v___x_4282_, 1, v___x_4281_);
                v_a_4171_ = v___x_4282_;
                state = 2;
                continue;
            }
            21 => {
                if v_isShared_4287_ == 0 {
                    v___x_4289_ = v___x_4286_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4289_;
            }
            23 => {
                if v_isShared_4295_ == 0 {
                    v___x_4297_ = v___x_4294_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
                    v___x_4297_ = v_reuseFailAlloc_4298_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4297_;
            }
            25 => {
                if v_isShared_4303_ == 0 {
                    v___x_4305_ = v___x_4302_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
                    v___x_4305_ = v_reuseFailAlloc_4306_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4305_;
            }
            27 => {
                if v_isShared_4314_ == 0 {
                    v___x_4316_ = v___x_4313_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
                    v___x_4316_ = v_reuseFailAlloc_4317_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4316_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__9___boxed(
    mut v_mvarId_4322_: *mut LeanObject,
    mut v_as_4323_: *mut LeanObject,
    mut v_sz_4324_: *mut LeanObject,
    mut v_i_4325_: *mut LeanObject,
    mut v_b_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
    mut v___y_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4332_: usize = 0;
    let mut v_i_boxed_4333_: usize = 0;
    let mut v_res_4334_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4332_ = lean_unbox_usize(v_sz_4324_);
    lean_dec(v_sz_4324_);
    v_i_boxed_4333_ = lean_unbox_usize(v_i_4325_);
    lean_dec(v_i_4325_);
    v_res_4334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__9(v_mvarId_4322_, v_as_4323_, v_sz_boxed_4332_, v_i_boxed_4333_, v_b_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
    lean_dec(v___y_4330_);
    lean_dec_ref(v___y_4329_);
    lean_dec(v___y_4328_);
    lean_dec_ref(v___y_4327_);
    lean_dec_ref(v_as_4323_);
    return v_res_4334_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3(
    mut v_mvarId_4335_: *mut LeanObject,
    mut v_t_4336_: *mut LeanObject,
    mut v_init_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4349_: u8 = 0;
    let mut v_a_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4357_: usize = 0;
    let mut v___x_4358_: usize = 0;
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4363_: u8 = 0;
    let mut v_fst_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4373_: u8 = 0;
    let mut v_a_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4377_: u8 = 0;
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4381_: u8 = 0;
    let mut v_isSharedCheck_4382_: u8 = 0;
    let mut v_a_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4386_: u8 = 0;
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4343_ = lean_ctor_get(v_t_4336_, 0);
                v_tail_4344_ = lean_ctor_get(v_t_4336_, 1);
                lean_inc(v_mvarId_4335_);
                lean_inc_ref(v_init_4337_);
                v___x_4345_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__8(v_init_4337_, v_mvarId_4335_, v_root_4343_, v_init_4337_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
                lean_dec_ref(v_init_4337_);
                if lean_obj_tag(v___x_4345_) == 0 {
                    v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
                    v_isSharedCheck_4382_ = (!lean_is_exclusive(v___x_4345_)) as u8;
                    if v_isSharedCheck_4382_ == 0 {
                        v___x_4348_ = v___x_4345_;
                        v_isShared_4349_ = v_isSharedCheck_4382_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4346_);
                        lean_dec(v___x_4345_);
                        v___x_4348_ = lean_box(0);
                        v_isShared_4349_ = v_isSharedCheck_4382_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_4335_);
                    v_a_4383_ = lean_ctor_get(v___x_4345_, 0);
                    v_isSharedCheck_4390_ = (!lean_is_exclusive(v___x_4345_)) as u8;
                    if v_isSharedCheck_4390_ == 0 {
                        v___x_4385_ = v___x_4345_;
                        v_isShared_4386_ = v_isSharedCheck_4390_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4383_);
                        lean_dec(v___x_4345_);
                        v___x_4385_ = lean_box(0);
                        v_isShared_4386_ = v_isSharedCheck_4390_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4346_) == 0 {
                    lean_dec(v_mvarId_4335_);
                    v_a_4350_ = lean_ctor_get(v_a_4346_, 0);
                    lean_inc(v_a_4350_);
                    lean_dec_ref_known(v_a_4346_, 1);
                    if v_isShared_4349_ == 0 {
                        lean_ctor_set(v___x_4348_, 0, v_a_4350_);
                        v___x_4352_ = v___x_4348_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4350_);
                        v___x_4352_ = v_reuseFailAlloc_4353_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4348_);
                    v_a_4354_ = lean_ctor_get(v_a_4346_, 0);
                    lean_inc(v_a_4354_);
                    lean_dec_ref_known(v_a_4346_, 1);
                    v___x_4355_ = lean_box(0);
                    v___x_4356_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4356_, 0, v___x_4355_);
                    lean_ctor_set(v___x_4356_, 1, v_a_4354_);
                    v_sz_4357_ = lean_array_size(v_tail_4344_);
                    v___x_4358_ = 0usize;
                    v___x_4359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3_spec__9(v_mvarId_4335_, v_tail_4344_, v_sz_4357_, v___x_4358_, v___x_4356_, v___y_4338_, v___y_4339_, v___y_4340_, v___y_4341_);
                    if lean_obj_tag(v___x_4359_) == 0 {
                        v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
                        v_isSharedCheck_4373_ = (!lean_is_exclusive(v___x_4359_)) as u8;
                        if v_isSharedCheck_4373_ == 0 {
                            v___x_4362_ = v___x_4359_;
                            v_isShared_4363_ = v_isSharedCheck_4373_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4360_);
                            lean_dec(v___x_4359_);
                            v___x_4362_ = lean_box(0);
                            v_isShared_4363_ = v_isSharedCheck_4373_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4374_ = lean_ctor_get(v___x_4359_, 0);
                        v_isSharedCheck_4381_ = (!lean_is_exclusive(v___x_4359_)) as u8;
                        if v_isSharedCheck_4381_ == 0 {
                            v___x_4376_ = v___x_4359_;
                            v_isShared_4377_ = v_isSharedCheck_4381_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4374_);
                            lean_dec(v___x_4359_);
                            v___x_4376_ = lean_box(0);
                            v_isShared_4377_ = v_isSharedCheck_4381_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4352_;
            }
            3 => {
                v_fst_4364_ = lean_ctor_get(v_a_4360_, 0);
                if lean_obj_tag(v_fst_4364_) == 0 {
                    v_snd_4365_ = lean_ctor_get(v_a_4360_, 1);
                    lean_inc(v_snd_4365_);
                    lean_dec(v_a_4360_);
                    if v_isShared_4363_ == 0 {
                        lean_ctor_set(v___x_4362_, 0, v_snd_4365_);
                        v___x_4367_ = v___x_4362_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_snd_4365_);
                        v___x_4367_ = v_reuseFailAlloc_4368_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_4364_);
                    lean_dec(v_a_4360_);
                    v_val_4369_ = lean_ctor_get(v_fst_4364_, 0);
                    lean_inc(v_val_4369_);
                    lean_dec_ref_known(v_fst_4364_, 1);
                    if v_isShared_4363_ == 0 {
                        lean_ctor_set(v___x_4362_, 0, v_val_4369_);
                        v___x_4371_ = v___x_4362_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4372_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_val_4369_);
                        v___x_4371_ = v_reuseFailAlloc_4372_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4367_;
            }
            5 => {
                return v___x_4371_;
            }
            6 => {
                if v_isShared_4377_ == 0 {
                    v___x_4379_ = v___x_4376_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
                    v___x_4379_ = v_reuseFailAlloc_4380_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4379_;
            }
            8 => {
                if v_isShared_4386_ == 0 {
                    v___x_4388_ = v___x_4385_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
                    v___x_4388_ = v_reuseFailAlloc_4389_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3___boxed(
    mut v_mvarId_4391_: *mut LeanObject,
    mut v_t_4392_: *mut LeanObject,
    mut v_init_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4399_: *mut LeanObject = core::ptr::null_mut();
    v_res_4399_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3(v_mvarId_4391_, v_t_4392_, v_init_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
    lean_dec(v___y_4397_);
    lean_dec_ref(v___y_4396_);
    lean_dec(v___y_4395_);
    lean_dec_ref(v___y_4394_);
    lean_dec_ref(v_t_4392_);
    return v_res_4399_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___lam__0(
    mut v_posMap_4400_: *mut LeanObject,
    mut v_mvarId_4401_: *mut LeanObject,
    mut v___y_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
    mut v___y_4405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v_fst_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: u8 = 0;
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4427_: u8 = 0;
    let mut v_a_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_4407_ = lean_ctor_get(v___y_4402_, 2);
                lean_inc_ref(v_posMap_4400_);
                v___x_4408_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4408_, 0, v_posMap_4400_);
                lean_ctor_set(v___x_4408_, 1, v_posMap_4400_);
                v_decls_4409_ = lean_ctor_get(v_lctx_4407_, 1);
                v___x_4410_ = lean_box(0);
                v___x_4411_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4411_, 0, v___x_4410_);
                lean_ctor_set(v___x_4411_, 1, v___x_4408_);
                v___x_4412_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__3(v_mvarId_4401_, v_decls_4409_, v___x_4411_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
                if lean_obj_tag(v___x_4412_) == 0 {
                    v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
                    v_isSharedCheck_4427_ = (!lean_is_exclusive(v___x_4412_)) as u8;
                    if v_isSharedCheck_4427_ == 0 {
                        v___x_4415_ = v___x_4412_;
                        v_isShared_4416_ = v_isSharedCheck_4427_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4413_);
                        lean_dec(v___x_4412_);
                        v___x_4415_ = lean_box(0);
                        v_isShared_4416_ = v_isSharedCheck_4427_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4428_ = lean_ctor_get(v___x_4412_, 0);
                    v_isSharedCheck_4435_ = (!lean_is_exclusive(v___x_4412_)) as u8;
                    if v_isSharedCheck_4435_ == 0 {
                        v___x_4430_ = v___x_4412_;
                        v_isShared_4431_ = v_isSharedCheck_4435_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4428_);
                        lean_dec(v___x_4412_);
                        v___x_4430_ = lean_box(0);
                        v_isShared_4431_ = v_isSharedCheck_4435_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4417_ = lean_ctor_get(v_a_4413_, 0);
                lean_inc(v_fst_4417_);
                lean_dec(v_a_4413_);
                if lean_obj_tag(v_fst_4417_) == 0 {
                    v___x_4418_ = 0;
                    v___x_4419_ = lean_box((v___x_4418_) as usize);
                    if v_isShared_4416_ == 0 {
                        lean_ctor_set(v___x_4415_, 0, v___x_4419_);
                        v___x_4421_ = v___x_4415_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4422_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4422_, 0, v___x_4419_);
                        v___x_4421_ = v_reuseFailAlloc_4422_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_4423_ = lean_ctor_get(v_fst_4417_, 0);
                    lean_inc(v_val_4423_);
                    lean_dec_ref_known(v_fst_4417_, 1);
                    if v_isShared_4416_ == 0 {
                        lean_ctor_set(v___x_4415_, 0, v_val_4423_);
                        v___x_4425_ = v___x_4415_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_val_4423_);
                        v___x_4425_ = v_reuseFailAlloc_4426_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4421_;
            }
            3 => {
                return v___x_4425_;
            }
            4 => {
                if v_isShared_4431_ == 0 {
                    v___x_4433_ = v___x_4430_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
                    v___x_4433_ = v_reuseFailAlloc_4434_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___lam__0___boxed(
    mut v_posMap_4436_: *mut LeanObject,
    mut v_mvarId_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
    mut v___y_4442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4443_: *mut LeanObject = core::ptr::null_mut();
    v_res_4443_ =
        l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___lam__0(
            v_posMap_4436_,
            v_mvarId_4437_,
            v___y_4438_,
            v___y_4439_,
            v___y_4440_,
            v___y_4441_,
        );
    lean_dec(v___y_4441_);
    lean_dec_ref(v___y_4440_);
    lean_dec(v___y_4439_);
    lean_dec_ref(v___y_4438_);
    return v_res_4443_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__0()
-> *mut LeanObject {
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    v___x_4444_ = lean_box(0);
    v___x_4445_ = lean_unsigned_to_nat(16);
    v___x_4446_ = lean_mk_array(v___x_4445_, v___x_4444_);
    return v___x_4446_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__1()
-> *mut LeanObject {
    let mut v___x_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_posMap_4449_: *mut LeanObject = core::ptr::null_mut();
    v___x_4447_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__0_once), _init_l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__0);
    v___x_4448_ = lean_unsigned_to_nat(0);
    v_posMap_4449_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_posMap_4449_, 0, v___x_4448_);
    lean_ctor_set(v_posMap_4449_, 1, v___x_4447_);
    return v_posMap_4449_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick(
    mut v_mvarId_4450_: *mut LeanObject,
    mut v_a_4451_: *mut LeanObject,
    mut v_a_4452_: *mut LeanObject,
    mut v_a_4453_: *mut LeanObject,
    mut v_a_4454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_posMap_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
    v_posMap_4456_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__1_once), _init_l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___closed__1);
    lean_inc(v_mvarId_4450_);
    v___f_4457_ = lean_alloc_closure(
        l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_4457_, 0, v_posMap_4456_);
    lean_closure_set(v___f_4457_, 1, v_mvarId_4450_);
    v___x_4458_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__4___redArg(v_mvarId_4450_, v___f_4457_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
    return v___x_4458_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick___boxed(
    mut v_mvarId_4459_: *mut LeanObject,
    mut v_a_4460_: *mut LeanObject,
    mut v_a_4461_: *mut LeanObject,
    mut v_a_4462_: *mut LeanObject,
    mut v_a_4463_: *mut LeanObject,
    mut v_a_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4465_: *mut LeanObject = core::ptr::null_mut();
    v_res_4465_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick(
        v_mvarId_4459_,
        v_a_4460_,
        v_a_4461_,
        v_a_4462_,
        v_a_4463_,
    );
    lean_dec(v_a_4463_);
    lean_dec_ref(v_a_4462_);
    lean_dec(v_a_4461_);
    lean_dec_ref(v_a_4460_);
    return v_res_4465_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0(
    mut v_00_u03b2_4466_: *mut LeanObject,
    mut v_m_4467_: *mut LeanObject,
    mut v_a_4468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    v___x_4469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___redArg(v_m_4467_, v_a_4468_);
    return v___x_4469_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0___boxed(
    mut v_00_u03b2_4470_: *mut LeanObject,
    mut v_m_4471_: *mut LeanObject,
    mut v_a_4472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4473_: *mut LeanObject = core::ptr::null_mut();
    v_res_4473_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0(v_00_u03b2_4470_, v_m_4471_, v_a_4472_);
    lean_dec_ref(v_a_4472_);
    lean_dec_ref(v_m_4471_);
    return v_res_4473_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1(
    mut v_mvarId_4474_: *mut LeanObject,
    mut v_val_4475_: *mut LeanObject,
    mut v___y_4476_: *mut LeanObject,
    mut v___y_4477_: *mut LeanObject,
    mut v___y_4478_: *mut LeanObject,
    mut v___y_4479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    v___x_4481_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___redArg(v_mvarId_4474_, v_val_4475_, v___y_4477_);
    return v___x_4481_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1___boxed(
    mut v_mvarId_4482_: *mut LeanObject,
    mut v_val_4483_: *mut LeanObject,
    mut v___y_4484_: *mut LeanObject,
    mut v___y_4485_: *mut LeanObject,
    mut v___y_4486_: *mut LeanObject,
    mut v___y_4487_: *mut LeanObject,
    mut v___y_4488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4489_: *mut LeanObject = core::ptr::null_mut();
    v_res_4489_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1(v_mvarId_4482_, v_val_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
    lean_dec(v___y_4487_);
    lean_dec_ref(v___y_4486_);
    lean_dec(v___y_4485_);
    lean_dec_ref(v___y_4484_);
    return v_res_4489_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2(
    mut v_00_u03b2_4490_: *mut LeanObject,
    mut v_m_4491_: *mut LeanObject,
    mut v_a_4492_: *mut LeanObject,
    mut v_b_4493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    v___x_4494_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2___redArg(v_m_4491_, v_a_4492_, v_b_4493_);
    return v___x_4494_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0_spec__0(
    mut v_00_u03b2_4495_: *mut LeanObject,
    mut v_a_4496_: *mut LeanObject,
    mut v_x_4497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    v___x_4498_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0_spec__0___redArg(v_a_4496_, v_x_4497_);
    return v___x_4498_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0_spec__0___boxed(
    mut v_00_u03b2_4499_: *mut LeanObject,
    mut v_a_4500_: *mut LeanObject,
    mut v_x_4501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4502_: *mut LeanObject = core::ptr::null_mut();
    v_res_4502_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__0_spec__0(v_00_u03b2_4499_, v_a_4500_, v_x_4501_);
    lean_dec(v_x_4501_);
    lean_dec_ref(v_a_4500_);
    return v_res_4502_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2(
    mut v_00_u03b2_4503_: *mut LeanObject,
    mut v_x_4504_: *mut LeanObject,
    mut v_x_4505_: *mut LeanObject,
    mut v_x_4506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    v___x_4507_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2___redArg(v_x_4504_, v_x_4505_, v_x_4506_);
    return v___x_4507_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__4(
    mut v_00_u03b2_4508_: *mut LeanObject,
    mut v_a_4509_: *mut LeanObject,
    mut v_x_4510_: *mut LeanObject,
) -> u8 {
    let mut v___x_4511_: u8 = 0;
    v___x_4511_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__4___redArg(v_a_4509_, v_x_4510_);
    return v___x_4511_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__4___boxed(
    mut v_00_u03b2_4512_: *mut LeanObject,
    mut v_a_4513_: *mut LeanObject,
    mut v_x_4514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4515_: u8 = 0;
    let mut v_r_4516_: *mut LeanObject = core::ptr::null_mut();
    v_res_4515_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__4(v_00_u03b2_4512_, v_a_4513_, v_x_4514_);
    lean_dec(v_x_4514_);
    lean_dec_ref(v_a_4513_);
    v_r_4516_ = lean_box((v_res_4515_) as usize);
    return v_r_4516_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5(
    mut v_00_u03b2_4517_: *mut LeanObject,
    mut v_data_4518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    v___x_4519_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5___redArg(v_data_4518_);
    return v___x_4519_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__6(
    mut v_00_u03b2_4520_: *mut LeanObject,
    mut v_a_4521_: *mut LeanObject,
    mut v_b_4522_: *mut LeanObject,
    mut v_x_4523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    v___x_4524_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__6___redArg(v_a_4521_, v_b_4522_, v_x_4523_);
    return v___x_4524_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4(
    mut v_00_u03b2_4525_: *mut LeanObject,
    mut v_x_4526_: *mut LeanObject,
    mut v_x_4527_: usize,
    mut v_x_4528_: usize,
    mut v_x_4529_: *mut LeanObject,
    mut v_x_4530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    v___x_4531_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___redArg(v_x_4526_, v_x_4527_, v_x_4528_, v_x_4529_, v_x_4530_);
    return v___x_4531_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_4532_: *mut LeanObject,
    mut v_x_4533_: *mut LeanObject,
    mut v_x_4534_: *mut LeanObject,
    mut v_x_4535_: *mut LeanObject,
    mut v_x_4536_: *mut LeanObject,
    mut v_x_4537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_10807__boxed_4538_: usize = 0;
    let mut v_x_10808__boxed_4539_: usize = 0;
    let mut v_res_4540_: *mut LeanObject = core::ptr::null_mut();
    v_x_10807__boxed_4538_ = lean_unbox_usize(v_x_4534_);
    lean_dec(v_x_4534_);
    v_x_10808__boxed_4539_ = lean_unbox_usize(v_x_4535_);
    lean_dec(v_x_4535_);
    v_res_4540_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4(v_00_u03b2_4532_, v_x_4533_, v_x_10807__boxed_4538_, v_x_10808__boxed_4539_, v_x_4536_, v_x_4537_);
    return v_res_4540_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5_spec__8(
    mut v_00_u03b2_4541_: *mut LeanObject,
    mut v_i_4542_: *mut LeanObject,
    mut v_source_4543_: *mut LeanObject,
    mut v_target_4544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    v___x_4545_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5_spec__8___redArg(v_i_4542_, v_source_4543_, v_target_4544_);
    return v___x_4545_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__7(
    mut v_00_u03b2_4546_: *mut LeanObject,
    mut v_n_4547_: *mut LeanObject,
    mut v_k_4548_: *mut LeanObject,
    mut v_v_4549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    v___x_4550_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__7___redArg(v_n_4547_, v_k_4548_, v_v_4549_);
    return v___x_4550_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__8(
    mut v_00_u03b2_4551_: *mut LeanObject,
    mut v_depth_4552_: usize,
    mut v_keys_4553_: *mut LeanObject,
    mut v_vals_4554_: *mut LeanObject,
    mut v_heq_4555_: *mut LeanObject,
    mut v_i_4556_: *mut LeanObject,
    mut v_entries_4557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    v___x_4558_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__8___redArg(v_depth_4552_, v_keys_4553_, v_vals_4554_, v_i_4556_, v_entries_4557_);
    return v___x_4558_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_4559_: *mut LeanObject,
    mut v_depth_4560_: *mut LeanObject,
    mut v_keys_4561_: *mut LeanObject,
    mut v_vals_4562_: *mut LeanObject,
    mut v_heq_4563_: *mut LeanObject,
    mut v_i_4564_: *mut LeanObject,
    mut v_entries_4565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4566_: usize = 0;
    let mut v_res_4567_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4566_ = lean_unbox_usize(v_depth_4560_);
    lean_dec(v_depth_4560_);
    v_res_4567_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__8(v_00_u03b2_4559_, v_depth_boxed_4566_, v_keys_4561_, v_vals_4562_, v_heq_4563_, v_i_4564_, v_entries_4565_);
    lean_dec_ref(v_vals_4562_);
    lean_dec_ref(v_keys_4561_);
    return v_res_4567_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5_spec__8_spec__12(
    mut v_00_u03b2_4568_: *mut LeanObject,
    mut v_x_4569_: *mut LeanObject,
    mut v_x_4570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    v___x_4571_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__2_spec__5_spec__8_spec__12___redArg(v_x_4569_, v_x_4570_);
    return v___x_4571_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__7_spec__13(
    mut v_00_u03b2_4572_: *mut LeanObject,
    mut v_x_4573_: *mut LeanObject,
    mut v_x_4574_: *mut LeanObject,
    mut v_x_4575_: *mut LeanObject,
    mut v_x_4576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    v___x_4577_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__1_spec__2_spec__4_spec__7_spec__13___redArg(v_x_4573_, v_x_4574_, v_x_4575_, v_x_4576_);
    return v___x_4577_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorIdx(
    mut v_x_4578_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_4578_) {
        0 => {
            let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
            v___x_4579_ = lean_unsigned_to_nat(0);
            return v___x_4579_;
        }
        1 => {
            let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
            v___x_4580_ = lean_unsigned_to_nat(1);
            return v___x_4580_;
        }
        _ => {
            let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
            v___x_4581_ = lean_unsigned_to_nat(2);
            return v___x_4581_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorIdx___boxed(
    mut v_x_4582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4583_: *mut LeanObject = core::ptr::null_mut();
    v_res_4583_ =
        l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorIdx(
            v_x_4582_,
        );
    lean_dec(v_x_4582_);
    return v_res_4583_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim___redArg(
    mut v_t_4584_: *mut LeanObject,
    mut v_k_4585_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_4584_) == 2 {
        let mut v_fvarId_4586_: *mut LeanObject = core::ptr::null_mut();
        let mut v_mvarId_4587_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_4586_ = lean_ctor_get(v_t_4584_, 0);
        lean_inc(v_fvarId_4586_);
        v_mvarId_4587_ = lean_ctor_get(v_t_4584_, 1);
        lean_inc(v_mvarId_4587_);
        lean_dec_ref_known(v_t_4584_, 2);
        v___x_4588_ = lean_apply_2(v_k_4585_, v_fvarId_4586_, v_mvarId_4587_);
        return v___x_4588_;
    } else {
        lean_dec(v_t_4584_);
        return v_k_4585_;
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim(
    mut v_motive_4589_: *mut LeanObject,
    mut v_ctorIdx_4590_: *mut LeanObject,
    mut v_t_4591_: *mut LeanObject,
    mut v_h_4592_: *mut LeanObject,
    mut v_k_4593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    v___x_4594_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim___redArg(v_t_4591_, v_k_4593_);
    return v___x_4594_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim___boxed(
    mut v_motive_4595_: *mut LeanObject,
    mut v_ctorIdx_4596_: *mut LeanObject,
    mut v_t_4597_: *mut LeanObject,
    mut v_h_4598_: *mut LeanObject,
    mut v_k_4599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4600_: *mut LeanObject = core::ptr::null_mut();
    v_res_4600_ =
        l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim(
            v_motive_4595_,
            v_ctorIdx_4596_,
            v_t_4597_,
            v_h_4598_,
            v_k_4599_,
        );
    lean_dec(v_ctorIdx_4596_);
    return v_res_4600_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_solved_elim___redArg(
    mut v_t_4601_: *mut LeanObject,
    mut v_solved_4602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    v___x_4603_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim___redArg(v_t_4601_, v_solved_4602_);
    return v___x_4603_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_solved_elim(
    mut v_motive_4604_: *mut LeanObject,
    mut v_t_4605_: *mut LeanObject,
    mut v_h_4606_: *mut LeanObject,
    mut v_solved_4607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    v___x_4608_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim___redArg(v_t_4605_, v_solved_4607_);
    return v___x_4608_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_failed_elim___redArg(
    mut v_t_4609_: *mut LeanObject,
    mut v_failed_4610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    v___x_4611_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim___redArg(v_t_4609_, v_failed_4610_);
    return v___x_4611_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_failed_elim(
    mut v_motive_4612_: *mut LeanObject,
    mut v_t_4613_: *mut LeanObject,
    mut v_h_4614_: *mut LeanObject,
    mut v_failed_4615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    v___x_4616_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim___redArg(v_t_4613_, v_failed_4615_);
    return v___x_4616_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_subgoal_elim___redArg(
    mut v_t_4617_: *mut LeanObject,
    mut v_subgoal_4618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    v___x_4619_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim___redArg(v_t_4617_, v_subgoal_4618_);
    return v___x_4619_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_subgoal_elim(
    mut v_motive_4620_: *mut LeanObject,
    mut v_t_4621_: *mut LeanObject,
    mut v_h_4622_: *mut LeanObject,
    mut v_subgoal_4623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    v___x_4624_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_InjectionAnyResult_ctorElim___redArg(v_t_4621_, v_subgoal_4623_);
    return v___x_4624_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAnyCandidate_x3f(
    mut v_type_4625_: *mut LeanObject,
    mut v_a_4626_: *mut LeanObject,
    mut v_a_4627_: *mut LeanObject,
    mut v_a_4628_: *mut LeanObject,
    mut v_a_4629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4638_: u8 = 0;
    let mut v_val_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v_snd_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4650_: u8 = 0;
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4656_: u8 = 0;
    let mut v_snd_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4665_: u8 = 0;
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4670_: u8 = 0;
    let mut v___x_4671_: u8 = 0;
    let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4681_: u8 = 0;
    let mut v_a_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4685_: u8 = 0;
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4689_: u8 = 0;
    let mut v_isSharedCheck_4690_: u8 = 0;
    let mut v_isSharedCheck_4691_: u8 = 0;
    let mut v_a_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4695_: u8 = 0;
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4699_: u8 = 0;
    let mut v_isSharedCheck_4700_: u8 = 0;
    let mut v_a_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4704_: u8 = 0;
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_4625_);
                v___x_4634_ = l_Lean_Meta_matchEq_x3f(
                    v_type_4625_,
                    v_a_4626_,
                    v_a_4627_,
                    v_a_4628_,
                    v_a_4629_,
                );
                if lean_obj_tag(v___x_4634_) == 0 {
                    v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4700_ = (!lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4700_ == 0 {
                        v___x_4637_ = v___x_4634_;
                        v_isShared_4638_ = v_isSharedCheck_4700_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4635_);
                        lean_dec(v___x_4634_);
                        v___x_4637_ = lean_box(0);
                        v_isShared_4638_ = v_isSharedCheck_4700_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_4625_);
                    v_a_4701_ = lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4708_ = (!lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4708_ == 0 {
                        v___x_4703_ = v___x_4634_;
                        v_isShared_4704_ = v_isSharedCheck_4708_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_4701_);
                        lean_dec(v___x_4634_);
                        v___x_4703_ = lean_box(0);
                        v_isShared_4704_ = v_isSharedCheck_4708_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4632_ = lean_box(0);
                v___x_4633_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4633_, 0, v___x_4632_);
                return v___x_4633_;
            }
            2 => {
                if lean_obj_tag(v_a_4635_) == 1 {
                    lean_dec_ref(v_type_4625_);
                    v_val_4639_ = lean_ctor_get(v_a_4635_, 0);
                    v_isSharedCheck_4650_ = (!lean_is_exclusive(v_a_4635_)) as u8;
                    if v_isSharedCheck_4650_ == 0 {
                        v___x_4641_ = v_a_4635_;
                        v_isShared_4642_ = v_isSharedCheck_4650_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_4639_);
                        lean_dec(v_a_4635_);
                        v___x_4641_ = lean_box(0);
                        v_isShared_4642_ = v_isSharedCheck_4650_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4637_);
                    lean_dec(v_a_4635_);
                    v___x_4651_ = l_Lean_Meta_matchHEq_x3f(
                        v_type_4625_,
                        v_a_4626_,
                        v_a_4627_,
                        v_a_4628_,
                        v_a_4629_,
                    );
                    if lean_obj_tag(v___x_4651_) == 0 {
                        v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
                        lean_inc(v_a_4652_);
                        lean_dec_ref_known(v___x_4651_, 1);
                        if lean_obj_tag(v_a_4652_) == 1 {
                            v_val_4653_ = lean_ctor_get(v_a_4652_, 0);
                            v_isSharedCheck_4691_ = (!lean_is_exclusive(v_a_4652_)) as u8;
                            if v_isSharedCheck_4691_ == 0 {
                                v___x_4655_ = v_a_4652_;
                                v_isShared_4656_ = v_isSharedCheck_4691_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_val_4653_);
                                lean_dec(v_a_4652_);
                                v___x_4655_ = lean_box(0);
                                v_isShared_4656_ = v_isSharedCheck_4691_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4652_);
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4692_ = lean_ctor_get(v___x_4651_, 0);
                        v_isSharedCheck_4699_ = (!lean_is_exclusive(v___x_4651_)) as u8;
                        if v_isSharedCheck_4699_ == 0 {
                            v___x_4694_ = v___x_4651_;
                            v_isShared_4695_ = v_isSharedCheck_4699_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_4692_);
                            lean_dec(v___x_4651_);
                            v___x_4694_ = lean_box(0);
                            v_isShared_4695_ = v_isSharedCheck_4699_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_snd_4643_ = lean_ctor_get(v_val_4639_, 1);
                lean_inc(v_snd_4643_);
                lean_dec(v_val_4639_);
                if v_isShared_4642_ == 0 {
                    lean_ctor_set(v___x_4641_, 0, v_snd_4643_);
                    v___x_4645_ = v___x_4641_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4649_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_snd_4643_);
                    v___x_4645_ = v_reuseFailAlloc_4649_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4638_ == 0 {
                    lean_ctor_set(v___x_4637_, 0, v___x_4645_);
                    v___x_4647_ = v___x_4637_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4645_);
                    v___x_4647_ = v_reuseFailAlloc_4648_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4647_;
            }
            6 => {
                v_snd_4657_ = lean_ctor_get(v_val_4653_, 1);
                lean_inc(v_snd_4657_);
                v_snd_4658_ = lean_ctor_get(v_snd_4657_, 1);
                lean_inc(v_snd_4658_);
                v_fst_4659_ = lean_ctor_get(v_val_4653_, 0);
                lean_inc(v_fst_4659_);
                lean_dec(v_val_4653_);
                v_fst_4660_ = lean_ctor_get(v_snd_4657_, 0);
                lean_inc(v_fst_4660_);
                lean_dec(v_snd_4657_);
                v_fst_4661_ = lean_ctor_get(v_snd_4658_, 0);
                v_snd_4662_ = lean_ctor_get(v_snd_4658_, 1);
                v_isSharedCheck_4690_ = (!lean_is_exclusive(v_snd_4658_)) as u8;
                if v_isSharedCheck_4690_ == 0 {
                    v___x_4664_ = v_snd_4658_;
                    v_isShared_4665_ = v_isSharedCheck_4690_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_snd_4662_);
                    lean_inc(v_fst_4661_);
                    lean_dec(v_snd_4658_);
                    v___x_4664_ = lean_box(0);
                    v_isShared_4665_ = v_isSharedCheck_4690_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4666_ = l_Lean_Meta_isExprDefEq(
                    v_fst_4659_,
                    v_fst_4661_,
                    v_a_4626_,
                    v_a_4627_,
                    v_a_4628_,
                    v_a_4629_,
                );
                if lean_obj_tag(v___x_4666_) == 0 {
                    v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
                    v_isSharedCheck_4681_ = (!lean_is_exclusive(v___x_4666_)) as u8;
                    if v_isSharedCheck_4681_ == 0 {
                        v___x_4669_ = v___x_4666_;
                        v_isShared_4670_ = v_isSharedCheck_4681_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4667_);
                        lean_dec(v___x_4666_);
                        v___x_4669_ = lean_box(0);
                        v_isShared_4670_ = v_isSharedCheck_4681_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4664_);
                    lean_dec(v_snd_4662_);
                    lean_dec(v_fst_4660_);
                    lean_del_object(v___x_4655_);
                    v_a_4682_ = lean_ctor_get(v___x_4666_, 0);
                    v_isSharedCheck_4689_ = (!lean_is_exclusive(v___x_4666_)) as u8;
                    if v_isSharedCheck_4689_ == 0 {
                        v___x_4684_ = v___x_4666_;
                        v_isShared_4685_ = v_isSharedCheck_4689_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_4682_);
                        lean_dec(v___x_4666_);
                        v___x_4684_ = lean_box(0);
                        v_isShared_4685_ = v_isSharedCheck_4689_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                v___x_4671_ = (lean_unbox(v_a_4667_) as u8);
                lean_dec(v_a_4667_);
                if v___x_4671_ == 0 {
                    lean_del_object(v___x_4669_);
                    lean_del_object(v___x_4664_);
                    lean_dec(v_snd_4662_);
                    lean_dec(v_fst_4660_);
                    lean_del_object(v___x_4655_);
                    state = 1;
                    continue;
                } else {
                    if v_isShared_4665_ == 0 {
                        lean_ctor_set(v___x_4664_, 0, v_fst_4660_);
                        v___x_4673_ = v___x_4664_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_fst_4660_);
                        lean_ctor_set(v_reuseFailAlloc_4680_, 1, v_snd_4662_);
                        v___x_4673_ = v_reuseFailAlloc_4680_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_4656_ == 0 {
                    lean_ctor_set(v___x_4655_, 0, v___x_4673_);
                    v___x_4675_ = v___x_4655_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4673_);
                    v___x_4675_ = v_reuseFailAlloc_4679_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4670_ == 0 {
                    lean_ctor_set(v___x_4669_, 0, v___x_4675_);
                    v___x_4677_ = v___x_4669_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 0, v___x_4675_);
                    v___x_4677_ = v_reuseFailAlloc_4678_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4677_;
            }
            12 => {
                if v_isShared_4685_ == 0 {
                    v___x_4687_ = v___x_4684_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
                    v___x_4687_ = v_reuseFailAlloc_4688_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4687_;
            }
            14 => {
                if v_isShared_4695_ == 0 {
                    v___x_4697_ = v___x_4694_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4698_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4698_, 0, v_a_4692_);
                    v___x_4697_ = v_reuseFailAlloc_4698_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4697_;
            }
            16 => {
                if v_isShared_4704_ == 0 {
                    v___x_4706_ = v___x_4703_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4707_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4701_);
                    v___x_4706_ = v_reuseFailAlloc_4707_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAnyCandidate_x3f___boxed(
    mut v_type_4709_: *mut LeanObject,
    mut v_a_4710_: *mut LeanObject,
    mut v_a_4711_: *mut LeanObject,
    mut v_a_4712_: *mut LeanObject,
    mut v_a_4713_: *mut LeanObject,
    mut v_a_4714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4715_: *mut LeanObject = core::ptr::null_mut();
    v_res_4715_ =
        l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAnyCandidate_x3f(
            v_type_4709_,
            v_a_4710_,
            v_a_4711_,
            v_a_4712_,
            v_a_4713_,
        );
    lean_dec(v_a_4713_);
    lean_dec_ref(v_a_4712_);
    lean_dec(v_a_4711_);
    lean_dec_ref(v_a_4710_);
    return v_res_4715_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1_spec__1(
    mut v_msgData_4716_: *mut LeanObject,
    mut v___y_4717_: *mut LeanObject,
    mut v___y_4718_: *mut LeanObject,
    mut v___y_4719_: *mut LeanObject,
    mut v___y_4720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    v___x_4722_ = lean_st_ref_get(v___y_4720_);
    v_env_4723_ = lean_ctor_get(v___x_4722_, 0);
    lean_inc_ref(v_env_4723_);
    lean_dec(v___x_4722_);
    v___x_4724_ = lean_st_ref_get(v___y_4718_);
    v_mctx_4725_ = lean_ctor_get(v___x_4724_, 0);
    lean_inc_ref(v_mctx_4725_);
    lean_dec(v___x_4724_);
    v_lctx_4726_ = lean_ctor_get(v___y_4717_, 2);
    v_options_4727_ = lean_ctor_get(v___y_4719_, 2);
    lean_inc_ref(v_options_4727_);
    lean_inc_ref(v_lctx_4726_);
    v___x_4728_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4728_, 0, v_env_4723_);
    lean_ctor_set(v___x_4728_, 1, v_mctx_4725_);
    lean_ctor_set(v___x_4728_, 2, v_lctx_4726_);
    lean_ctor_set(v___x_4728_, 3, v_options_4727_);
    v___x_4729_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4729_, 0, v___x_4728_);
    lean_ctor_set(v___x_4729_, 1, v_msgData_4716_);
    v___x_4730_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4730_, 0, v___x_4729_);
    return v___x_4730_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1_spec__1___boxed(
    mut v_msgData_4731_: *mut LeanObject,
    mut v___y_4732_: *mut LeanObject,
    mut v___y_4733_: *mut LeanObject,
    mut v___y_4734_: *mut LeanObject,
    mut v___y_4735_: *mut LeanObject,
    mut v___y_4736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4737_: *mut LeanObject = core::ptr::null_mut();
    v_res_4737_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1_spec__1(v_msgData_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_);
    lean_dec(v___y_4735_);
    lean_dec_ref(v___y_4734_);
    lean_dec(v___y_4733_);
    lean_dec_ref(v___y_4732_);
    return v_res_4737_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__0()
-> f64 {
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: f64 = 0.0;
    v___x_4738_ = lean_unsigned_to_nat(0);
    v___x_4739_ = lean_float_of_nat(v___x_4738_);
    return v___x_4739_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1(
    mut v_cls_4743_: *mut LeanObject,
    mut v_msg_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
    mut v___y_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4755_: u8 = 0;
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4768_: u8 = 0;
    let mut v_tid_4769_: u64 = 0;
    let mut v_traces_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4773_: u8 = 0;
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: f64 = 0.0;
    let mut v___x_4776_: u8 = 0;
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4794_: u8 = 0;
    let mut v_isSharedCheck_4795_: u8 = 0;
    let mut v_isSharedCheck_4796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4750_ = lean_ctor_get(v___y_4747_, 5);
                v___x_4751_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1_spec__1(v_msg_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_);
                v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
                v_isSharedCheck_4796_ = (!lean_is_exclusive(v___x_4751_)) as u8;
                if v_isSharedCheck_4796_ == 0 {
                    v___x_4754_ = v___x_4751_;
                    v_isShared_4755_ = v_isSharedCheck_4796_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4752_);
                    lean_dec(v___x_4751_);
                    v___x_4754_ = lean_box(0);
                    v_isShared_4755_ = v_isSharedCheck_4796_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4756_ = lean_st_ref_take(v___y_4748_);
                v_traceState_4757_ = lean_ctor_get(v___x_4756_, 4);
                v_env_4758_ = lean_ctor_get(v___x_4756_, 0);
                v_nextMacroScope_4759_ = lean_ctor_get(v___x_4756_, 1);
                v_ngen_4760_ = lean_ctor_get(v___x_4756_, 2);
                v_auxDeclNGen_4761_ = lean_ctor_get(v___x_4756_, 3);
                v_cache_4762_ = lean_ctor_get(v___x_4756_, 5);
                v_messages_4763_ = lean_ctor_get(v___x_4756_, 6);
                v_infoState_4764_ = lean_ctor_get(v___x_4756_, 7);
                v_snapshotTasks_4765_ = lean_ctor_get(v___x_4756_, 8);
                v_isSharedCheck_4795_ = (!lean_is_exclusive(v___x_4756_)) as u8;
                if v_isSharedCheck_4795_ == 0 {
                    v___x_4767_ = v___x_4756_;
                    v_isShared_4768_ = v_isSharedCheck_4795_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4765_);
                    lean_inc(v_infoState_4764_);
                    lean_inc(v_messages_4763_);
                    lean_inc(v_cache_4762_);
                    lean_inc(v_traceState_4757_);
                    lean_inc(v_auxDeclNGen_4761_);
                    lean_inc(v_ngen_4760_);
                    lean_inc(v_nextMacroScope_4759_);
                    lean_inc(v_env_4758_);
                    lean_dec(v___x_4756_);
                    v___x_4767_ = lean_box(0);
                    v_isShared_4768_ = v_isSharedCheck_4795_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4769_ = lean_ctor_get_uint64(
                    v_traceState_4757_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4770_ = lean_ctor_get(v_traceState_4757_, 0);
                v_isSharedCheck_4794_ = (!lean_is_exclusive(v_traceState_4757_)) as u8;
                if v_isSharedCheck_4794_ == 0 {
                    v___x_4772_ = v_traceState_4757_;
                    v_isShared_4773_ = v_isSharedCheck_4794_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_4770_);
                    lean_dec(v_traceState_4757_);
                    v___x_4772_ = lean_box(0);
                    v_isShared_4773_ = v_isSharedCheck_4794_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4774_ = lean_box(0);
                v___x_4775_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__0);
                v___x_4776_ = 0;
                v___x_4777_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__1;
                v___x_4778_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4778_, 0, v_cls_4743_);
                lean_ctor_set(v___x_4778_, 1, v___x_4774_);
                lean_ctor_set(v___x_4778_, 2, v___x_4777_);
                lean_ctor_set_float(
                    v___x_4778_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4775_,
                );
                lean_ctor_set_float(
                    v___x_4778_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4775_,
                );
                lean_ctor_set_uint8(
                    v___x_4778_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4776_,
                );
                v___x_4779_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___closed__2;
                v___x_4780_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4780_, 0, v___x_4778_);
                lean_ctor_set(v___x_4780_, 1, v_a_4752_);
                lean_ctor_set(v___x_4780_, 2, v___x_4779_);
                lean_inc(v_ref_4750_);
                v___x_4781_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4781_, 0, v_ref_4750_);
                lean_ctor_set(v___x_4781_, 1, v___x_4780_);
                v___x_4782_ = l_Lean_PersistentArray_push___redArg(v_traces_4770_, v___x_4781_);
                if v_isShared_4773_ == 0 {
                    lean_ctor_set(v___x_4772_, 0, v___x_4782_);
                    v___x_4784_ = v___x_4772_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4782_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4793_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4769_,
                    );
                    v___x_4784_ = v_reuseFailAlloc_4793_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4768_ == 0 {
                    lean_ctor_set(v___x_4767_, 4, v___x_4784_);
                    v___x_4786_ = v___x_4767_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4792_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_env_4758_);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 1, v_nextMacroScope_4759_);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 2, v_ngen_4760_);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 3, v_auxDeclNGen_4761_);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 4, v___x_4784_);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 5, v_cache_4762_);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 6, v_messages_4763_);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 7, v_infoState_4764_);
                    lean_ctor_set(v_reuseFailAlloc_4792_, 8, v_snapshotTasks_4765_);
                    v___x_4786_ = v_reuseFailAlloc_4792_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4787_ = lean_st_ref_set(v___y_4748_, v___x_4786_);
                v___x_4788_ = lean_box(0);
                if v_isShared_4755_ == 0 {
                    lean_ctor_set(v___x_4754_, 0, v___x_4788_);
                    v___x_4790_ = v___x_4754_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4791_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4791_, 0, v___x_4788_);
                    v___x_4790_ = v_reuseFailAlloc_4791_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4790_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1___boxed(
    mut v_cls_4797_: *mut LeanObject,
    mut v_msg_4798_: *mut LeanObject,
    mut v___y_4799_: *mut LeanObject,
    mut v___y_4800_: *mut LeanObject,
    mut v___y_4801_: *mut LeanObject,
    mut v___y_4802_: *mut LeanObject,
    mut v___y_4803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4804_: *mut LeanObject = core::ptr::null_mut();
    v_res_4804_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1(v_cls_4797_, v_msg_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
    lean_dec(v___y_4802_);
    lean_dec_ref(v___y_4801_);
    lean_dec(v___y_4800_);
    lean_dec_ref(v___y_4799_);
    return v_res_4804_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0___redArg(
    mut v_k_4805_: *mut LeanObject,
    mut v_t_4806_: *mut LeanObject,
) -> u8 {
    let mut v_k_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_4806_) == 0 {
                    v_k_4807_ = lean_ctor_get(v_t_4806_, 1);
                    v_l_4808_ = lean_ctor_get(v_t_4806_, 3);
                    v_r_4809_ = lean_ctor_get(v_t_4806_, 4);
                    v___x_4810_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4805_, v_k_4807_);
                    match v___x_4810_ {
                        0 => {
                            v_t_4806_ = v_l_4808_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_4812_ = 1;
                            return v___x_4812_;
                        }
                        _ => {
                            v_t_4806_ = v_r_4809_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_4814_ = 0;
                    return v___x_4814_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0___redArg___boxed(
    mut v_k_4815_: *mut LeanObject,
    mut v_t_4816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4817_: u8 = 0;
    let mut v_r_4818_: *mut LeanObject = core::ptr::null_mut();
    v_res_4817_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0___redArg(v_k_4815_, v_t_4816_);
    lean_dec(v_t_4816_);
    lean_dec(v_k_4815_);
    v_r_4818_ = lean_box((v_res_4817_) as usize);
    return v_r_4818_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0(
    mut v___x_4819_: *mut LeanObject,
    mut v_____r_4820_: *mut LeanObject,
    mut v___y_4821_: *mut LeanObject,
    mut v___y_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
    mut v___y_4824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    v___x_4826_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4826_, 0, v___x_4819_);
    v___x_4827_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4827_, 0, v___x_4826_);
    return v___x_4827_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0___boxed(
    mut v___x_4828_: *mut LeanObject,
    mut v_____r_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
    mut v___y_4831_: *mut LeanObject,
    mut v___y_4832_: *mut LeanObject,
    mut v___y_4833_: *mut LeanObject,
    mut v___y_4834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4835_: *mut LeanObject = core::ptr::null_mut();
    v_res_4835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0(v___x_4828_, v_____r_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_);
    lean_dec(v___y_4833_);
    lean_dec_ref(v___y_4832_);
    lean_dec(v___y_4831_);
    lean_dec_ref(v___y_4830_);
    return v_res_4835_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7()
-> *mut LeanObject {
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    v___x_4849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4;
    v___x_4850_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__6;
    v___x_4851_ = l_Lean_Name_append(v___x_4850_, v___x_4849_);
    return v___x_4851_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9()
-> *mut LeanObject {
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    v___x_4853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__8;
    v___x_4854_ = l_Lean_stringToMessageData(v___x_4853_);
    return v___x_4854_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11()
-> *mut LeanObject {
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    v___x_4856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__10;
    v___x_4857_ = l_Lean_stringToMessageData(v___x_4856_);
    return v___x_4857_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6(
    mut v_forbidden_4858_: *mut LeanObject,
    mut v_mvarId_4859_: *mut LeanObject,
    mut v_as_4860_: *mut LeanObject,
    mut v_sz_4861_: usize,
    mut v_i_4862_: usize,
    mut v_b_4863_: *mut LeanObject,
    mut v___y_4864_: *mut LeanObject,
    mut v___y_4865_: *mut LeanObject,
    mut v___y_4866_: *mut LeanObject,
    mut v___y_4867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4869_: u8 = 0;
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: usize = 0;
    let mut v___x_4881_: usize = 0;
    let mut v_reuseFailAlloc_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4888_: u8 = 0;
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4908_: u8 = 0;
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4912_: u8 = 0;
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: u8 = 0;
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4923_: u8 = 0;
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: u8 = 0;
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4933_: u8 = 0;
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4938_: u8 = 0;
    let mut v_options_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4940_: u8 = 0;
    let mut v_inheritedTraceOptions_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: u8 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4960_: u8 = 0;
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4964_: u8 = 0;
    let mut v_reuseFailAlloc_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4970_: u8 = 0;
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: u8 = 0;
    let mut v___x_4979_: u8 = 0;
    let mut v___x_4980_: u8 = 0;
    let mut v___x_4981_: u8 = 0;
    let mut v_isSharedCheck_4982_: u8 = 0;
    let mut v_a_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4986_: u8 = 0;
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4990_: u8 = 0;
    let mut v_a_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4994_: u8 = 0;
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4998_: u8 = 0;
    let mut v_a_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5002_: u8 = 0;
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5006_: u8 = 0;
    let mut v_isSharedCheck_5007_: u8 = 0;
    let mut v_a_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_isSharedCheck_5016_: u8 = 0;
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_unused_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4869_ = lean_usize_dec_lt(v_i_4862_, v_sz_4861_);
                if v___x_4869_ == 0 {
                    lean_dec(v_mvarId_4859_);
                    v___x_4870_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4870_, 0, v_b_4863_);
                    return v___x_4870_;
                } else {
                    v_snd_4871_ = lean_ctor_get(v_b_4863_, 1);
                    v_isSharedCheck_5017_ = (!lean_is_exclusive(v_b_4863_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v_unused_5018_ = lean_ctor_get(v_b_4863_, 0);
                        lean_dec(v_unused_5018_);
                        v___x_4873_ = v_b_4863_;
                        v_isShared_4874_ = v_isSharedCheck_5017_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4871_);
                        lean_dec(v_b_4863_);
                        v___x_4873_ = lean_box(0);
                        v_isShared_4874_ = v_isSharedCheck_5017_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4875_ = lean_box(0);
                v_a_4884_ = lean_array_uget(v_as_4860_, v_i_4862_);
                if lean_obj_tag(v_a_4884_) == 0 {
                    v_a_4877_ = v_snd_4871_;
                    state = 2;
                    continue;
                } else {
                    v_val_4885_ = lean_ctor_get(v_a_4884_, 0);
                    v_isSharedCheck_5016_ = (!lean_is_exclusive(v_a_4884_)) as u8;
                    if v_isSharedCheck_5016_ == 0 {
                        v___x_4887_ = v_a_4884_;
                        v_isShared_4888_ = v_isSharedCheck_5016_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_4885_);
                        lean_dec(v_a_4884_);
                        v___x_4887_ = lean_box(0);
                        v_isShared_4888_ = v_isSharedCheck_5016_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4874_ == 0 {
                    lean_ctor_set(v___x_4873_, 1, v_a_4877_);
                    lean_ctor_set(v___x_4873_, 0, v___x_4875_);
                    v___x_4879_ = v___x_4873_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4875_);
                    lean_ctor_set(v_reuseFailAlloc_4883_, 1, v_a_4877_);
                    v___x_4879_ = v_reuseFailAlloc_4883_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4880_ = 1usize;
                v___x_4881_ = lean_usize_add(v_i_4862_, v___x_4880_);
                v_i_4862_ = v___x_4881_;
                v_b_4863_ = v___x_4879_;
                state = 0;
                continue;
            }
            4 => {
                v___x_4889_ = lean_box(0);
                v___x_4900_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__0;
                v___x_4913_ = l_Lean_LocalDecl_fvarId(v_val_4885_);
                v___x_4914_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0___redArg(v___x_4913_, v_forbidden_4858_);
                if v___x_4914_ == 0 {
                    v___x_4915_ = l_Lean_LocalDecl_type(v_val_4885_);
                    v___x_4916_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAnyCandidate_x3f(v___x_4915_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
                    if lean_obj_tag(v___x_4916_) == 0 {
                        v_a_4917_ = lean_ctor_get(v___x_4916_, 0);
                        lean_inc(v_a_4917_);
                        lean_dec_ref_known(v___x_4916_, 1);
                        if lean_obj_tag(v_a_4917_) == 1 {
                            v_val_4918_ = lean_ctor_get(v_a_4917_, 0);
                            lean_inc(v_val_4918_);
                            lean_dec_ref_known(v_a_4917_, 1);
                            v_fst_4919_ = lean_ctor_get(v_val_4918_, 0);
                            v_snd_4920_ = lean_ctor_get(v_val_4918_, 1);
                            v_isSharedCheck_5007_ = (!lean_is_exclusive(v_val_4918_)) as u8;
                            if v_isSharedCheck_5007_ == 0 {
                                v___x_4922_ = v_val_4918_;
                                v_isShared_4923_ = v_isSharedCheck_5007_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_snd_4920_);
                                lean_inc(v_fst_4919_);
                                lean_dec(v_val_4918_);
                                v___x_4922_ = lean_box(0);
                                v_isShared_4923_ = v_isSharedCheck_5007_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4917_);
                            lean_dec(v___x_4913_);
                            lean_del_object(v___x_4887_);
                            lean_dec(v_val_4885_);
                            lean_dec(v_snd_4871_);
                            v_a_4877_ = v___x_4900_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4913_);
                        lean_del_object(v___x_4887_);
                        lean_dec(v_val_4885_);
                        lean_del_object(v___x_4873_);
                        lean_dec(v_snd_4871_);
                        lean_dec(v_mvarId_4859_);
                        v_a_5008_ = lean_ctor_get(v___x_4916_, 0);
                        v_isSharedCheck_5015_ = (!lean_is_exclusive(v___x_4916_)) as u8;
                        if v_isSharedCheck_5015_ == 0 {
                            v___x_5010_ = v___x_4916_;
                            v_isShared_5011_ = v_isSharedCheck_5015_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_5008_);
                            lean_dec(v___x_4916_);
                            v___x_5010_ = lean_box(0);
                            v_isShared_5011_ = v_isSharedCheck_5015_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_4913_);
                    lean_del_object(v___x_4887_);
                    lean_dec(v_val_4885_);
                    lean_dec(v_snd_4871_);
                    v_a_4877_ = v___x_4900_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_4888_ == 0 {
                    lean_ctor_set(v___x_4887_, 0, v_a_4891_);
                    v___x_4893_ = v___x_4887_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4891_);
                    v___x_4893_ = v_reuseFailAlloc_4899_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4894_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4894_, 0, v___x_4893_);
                lean_ctor_set(v___x_4894_, 1, v___x_4889_);
                v___x_4895_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4895_, 0, v___x_4894_);
                v___x_4896_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4896_, 0, v___x_4895_);
                v___x_4897_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4897_, 0, v___x_4896_);
                lean_ctor_set(v___x_4897_, 1, v_snd_4871_);
                v___x_4898_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4898_, 0, v___x_4897_);
                return v___x_4898_;
            }
            7 => {
                if lean_obj_tag(v___y_4902_) == 0 {
                    v_a_4903_ = lean_ctor_get(v___y_4902_, 0);
                    lean_inc(v_a_4903_);
                    lean_dec_ref_known(v___y_4902_, 1);
                    if lean_obj_tag(v_a_4903_) == 0 {
                        lean_del_object(v___x_4873_);
                        lean_dec(v_mvarId_4859_);
                        v_a_4904_ = lean_ctor_get(v_a_4903_, 0);
                        lean_inc(v_a_4904_);
                        lean_dec_ref_known(v_a_4903_, 1);
                        v_a_4891_ = v_a_4904_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec_ref_known(v_a_4903_, 1);
                        lean_del_object(v___x_4887_);
                        lean_dec(v_snd_4871_);
                        v_a_4877_ = v___x_4900_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4887_);
                    lean_del_object(v___x_4873_);
                    lean_dec(v_snd_4871_);
                    lean_dec(v_mvarId_4859_);
                    v_a_4905_ = lean_ctor_get(v___y_4902_, 0);
                    v_isSharedCheck_4912_ = (!lean_is_exclusive(v___y_4902_)) as u8;
                    if v_isSharedCheck_4912_ == 0 {
                        v___x_4907_ = v___y_4902_;
                        v_isShared_4908_ = v_isSharedCheck_4912_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4905_);
                        lean_dec(v___y_4902_);
                        v___x_4907_ = lean_box(0);
                        v_isShared_4908_ = v_isSharedCheck_4912_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_4908_ == 0 {
                    v___x_4910_ = v___x_4907_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
                    v___x_4910_ = v_reuseFailAlloc_4911_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4910_;
            }
            10 => {
                lean_inc(v_snd_4920_);
                lean_inc(v_fst_4919_);
                v___x_4924_ = l_Lean_Meta_isExprDefEq(
                    v_fst_4919_,
                    v_snd_4920_,
                    v___y_4864_,
                    v___y_4865_,
                    v___y_4866_,
                    v___y_4867_,
                );
                if lean_obj_tag(v___x_4924_) == 0 {
                    v_a_4925_ = lean_ctor_get(v___x_4924_, 0);
                    lean_inc(v_a_4925_);
                    lean_dec_ref_known(v___x_4924_, 1);
                    v___x_4926_ = (lean_unbox(v_a_4925_) as u8);
                    lean_dec(v_a_4925_);
                    if v___x_4926_ == 0 {
                        lean_inc(v___y_4867_);
                        lean_inc_ref(v___y_4866_);
                        lean_inc(v___y_4865_);
                        lean_inc_ref(v___y_4864_);
                        v___x_4927_ = lean_whnf(
                            v_fst_4919_,
                            v___y_4864_,
                            v___y_4865_,
                            v___y_4866_,
                            v___y_4867_,
                        );
                        if lean_obj_tag(v___x_4927_) == 0 {
                            v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
                            lean_inc(v_a_4928_);
                            lean_dec_ref_known(v___x_4927_, 1);
                            lean_inc(v___y_4867_);
                            lean_inc_ref(v___y_4866_);
                            lean_inc(v___y_4865_);
                            lean_inc_ref(v___y_4864_);
                            v___x_4929_ = lean_whnf(
                                v_snd_4920_,
                                v___y_4864_,
                                v___y_4865_,
                                v___y_4866_,
                                v___y_4867_,
                            );
                            if lean_obj_tag(v___x_4929_) == 0 {
                                v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
                                v_isSharedCheck_4982_ = (!lean_is_exclusive(v___x_4929_)) as u8;
                                if v_isSharedCheck_4982_ == 0 {
                                    v___x_4932_ = v___x_4929_;
                                    v_isShared_4933_ = v_isSharedCheck_4982_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_4930_);
                                    lean_dec(v___x_4929_);
                                    v___x_4932_ = lean_box(0);
                                    v_isShared_4933_ = v_isSharedCheck_4982_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4928_);
                                lean_del_object(v___x_4922_);
                                lean_dec(v___x_4913_);
                                lean_del_object(v___x_4887_);
                                lean_dec(v_val_4885_);
                                lean_del_object(v___x_4873_);
                                lean_dec(v_snd_4871_);
                                lean_dec(v_mvarId_4859_);
                                v_a_4983_ = lean_ctor_get(v___x_4929_, 0);
                                v_isSharedCheck_4990_ = (!lean_is_exclusive(v___x_4929_)) as u8;
                                if v_isSharedCheck_4990_ == 0 {
                                    v___x_4985_ = v___x_4929_;
                                    v_isShared_4986_ = v_isSharedCheck_4990_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_4983_);
                                    lean_dec(v___x_4929_);
                                    v___x_4985_ = lean_box(0);
                                    v_isShared_4986_ = v_isSharedCheck_4990_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_4922_);
                            lean_dec(v_snd_4920_);
                            lean_dec(v___x_4913_);
                            lean_del_object(v___x_4887_);
                            lean_dec(v_val_4885_);
                            lean_del_object(v___x_4873_);
                            lean_dec(v_snd_4871_);
                            lean_dec(v_mvarId_4859_);
                            v_a_4991_ = lean_ctor_get(v___x_4927_, 0);
                            v_isSharedCheck_4998_ = (!lean_is_exclusive(v___x_4927_)) as u8;
                            if v_isSharedCheck_4998_ == 0 {
                                v___x_4993_ = v___x_4927_;
                                v_isShared_4994_ = v_isSharedCheck_4998_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_4991_);
                                lean_dec(v___x_4927_);
                                v___x_4993_ = lean_box(0);
                                v_isShared_4994_ = v_isSharedCheck_4998_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4922_);
                        lean_dec(v_snd_4920_);
                        lean_dec(v_fst_4919_);
                        lean_dec(v___x_4913_);
                        lean_del_object(v___x_4887_);
                        lean_dec(v_val_4885_);
                        lean_dec(v_snd_4871_);
                        v_a_4877_ = v___x_4900_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4922_);
                    lean_dec(v_snd_4920_);
                    lean_dec(v_fst_4919_);
                    lean_dec(v___x_4913_);
                    lean_del_object(v___x_4887_);
                    lean_dec(v_val_4885_);
                    lean_del_object(v___x_4873_);
                    lean_dec(v_snd_4871_);
                    lean_dec(v_mvarId_4859_);
                    v_a_4999_ = lean_ctor_get(v___x_4924_, 0);
                    v_isSharedCheck_5006_ = (!lean_is_exclusive(v___x_4924_)) as u8;
                    if v_isSharedCheck_5006_ == 0 {
                        v___x_5001_ = v___x_4924_;
                        v_isShared_5002_ = v_isSharedCheck_5006_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_4999_);
                        lean_dec(v___x_4924_);
                        v___x_5001_ = lean_box(0);
                        v_isShared_5002_ = v_isSharedCheck_5006_;
                        state = 23;
                        continue;
                    }
                }
            }
            11 => {
                v___x_4980_ = l_Lean_Expr_isRawNatLit(v_a_4928_);
                lean_dec(v_a_4928_);
                if v___x_4980_ == 0 {
                    lean_dec(v_a_4930_);
                    v___y_4970_ = v___x_4980_;
                    state = 18;
                    continue;
                } else {
                    v___x_4981_ = l_Lean_Expr_isRawNatLit(v_a_4930_);
                    lean_dec(v_a_4930_);
                    v___y_4970_ = v___x_4981_;
                    state = 18;
                    continue;
                }
            }
            12 => {
                v___x_4935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0(v___x_4889_, v___x_4889_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
                v___y_4902_ = v___x_4935_;
                state = 7;
                continue;
            }
            13 => {
                if v___y_4938_ == 0 {
                    lean_del_object(v___x_4932_);
                    v_options_4939_ = lean_ctor_get(v___y_4866_, 2);
                    v_hasTrace_4940_ = lean_ctor_get_uint8(
                        v_options_4939_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4940_ == 0 {
                        lean_dec_ref(v___y_4937_);
                        lean_del_object(v___x_4922_);
                        lean_dec(v_val_4885_);
                        state = 12;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4941_ = lean_ctor_get(v___y_4866_, 13);
                        v___x_4942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4;
                        v___x_4943_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7);
                        v___x_4944_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4941_,
                            v_options_4939_,
                            v___x_4943_,
                        );
                        if v___x_4944_ == 0 {
                            lean_dec_ref(v___y_4937_);
                            lean_del_object(v___x_4922_);
                            lean_dec(v_val_4885_);
                            state = 12;
                            continue;
                        } else {
                            v___x_4945_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9);
                            v___x_4946_ = l_Lean_LocalDecl_userName(v_val_4885_);
                            lean_dec(v_val_4885_);
                            v___x_4947_ = l_Lean_MessageData_ofName(v___x_4946_);
                            if v_isShared_4923_ == 0 {
                                lean_ctor_set_tag(v___x_4922_, 7);
                                lean_ctor_set(v___x_4922_, 1, v___x_4947_);
                                lean_ctor_set(v___x_4922_, 0, v___x_4945_);
                                v___x_4949_ = v___x_4922_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_4965_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4965_, 0, v___x_4945_);
                                lean_ctor_set(v_reuseFailAlloc_4965_, 1, v___x_4947_);
                                v___x_4949_ = v_reuseFailAlloc_4965_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4922_);
                    lean_del_object(v___x_4887_);
                    lean_dec(v_val_4885_);
                    lean_del_object(v___x_4873_);
                    lean_dec(v_snd_4871_);
                    lean_dec(v_mvarId_4859_);
                    if v_isShared_4933_ == 0 {
                        lean_ctor_set_tag(v___x_4932_, 1);
                        lean_ctor_set(v___x_4932_, 0, v___y_4937_);
                        v___x_4967_ = v___x_4932_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___y_4937_);
                        v___x_4967_ = v_reuseFailAlloc_4968_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                v___x_4950_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11);
                v___x_4951_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4951_, 0, v___x_4949_);
                lean_ctor_set(v___x_4951_, 1, v___x_4950_);
                v___x_4952_ = l_Lean_Exception_toMessageData(v___y_4937_);
                v___x_4953_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4953_, 0, v___x_4951_);
                lean_ctor_set(v___x_4953_, 1, v___x_4952_);
                v___x_4954_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1(v___x_4942_, v___x_4953_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
                if lean_obj_tag(v___x_4954_) == 0 {
                    v_a_4955_ = lean_ctor_get(v___x_4954_, 0);
                    lean_inc(v_a_4955_);
                    lean_dec_ref_known(v___x_4954_, 1);
                    v___x_4956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0(v___x_4889_, v_a_4955_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
                    v___y_4902_ = v___x_4956_;
                    state = 7;
                    continue;
                } else {
                    lean_del_object(v___x_4887_);
                    lean_del_object(v___x_4873_);
                    lean_dec(v_snd_4871_);
                    lean_dec(v_mvarId_4859_);
                    v_a_4957_ = lean_ctor_get(v___x_4954_, 0);
                    v_isSharedCheck_4964_ = (!lean_is_exclusive(v___x_4954_)) as u8;
                    if v_isSharedCheck_4964_ == 0 {
                        v___x_4959_ = v___x_4954_;
                        v_isShared_4960_ = v_isSharedCheck_4964_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4957_);
                        lean_dec(v___x_4954_);
                        v___x_4959_ = lean_box(0);
                        v_isShared_4960_ = v_isSharedCheck_4964_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_4960_ == 0 {
                    v___x_4962_ = v___x_4959_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4963_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4963_, 0, v_a_4957_);
                    v___x_4962_ = v_reuseFailAlloc_4963_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4962_;
            }
            17 => {
                return v___x_4967_;
            }
            18 => {
                if v___y_4970_ == 0 {
                    v___x_4971_ = lean_box(0);
                    lean_inc(v___x_4913_);
                    lean_inc(v_mvarId_4859_);
                    v___x_4972_ = l_Lean_Meta_injection(
                        v_mvarId_4859_,
                        v___x_4913_,
                        v___x_4971_,
                        v___y_4864_,
                        v___y_4865_,
                        v___y_4866_,
                        v___y_4867_,
                    );
                    if lean_obj_tag(v___x_4972_) == 0 {
                        lean_del_object(v___x_4932_);
                        lean_del_object(v___x_4922_);
                        lean_dec(v_val_4885_);
                        lean_del_object(v___x_4873_);
                        lean_dec(v_mvarId_4859_);
                        v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
                        lean_inc(v_a_4973_);
                        lean_dec_ref_known(v___x_4972_, 1);
                        if lean_obj_tag(v_a_4973_) == 0 {
                            lean_dec(v___x_4913_);
                            v___x_4974_ = lean_box(0);
                            v_a_4891_ = v___x_4974_;
                            state = 5;
                            continue;
                        } else {
                            v_mvarId_4975_ = lean_ctor_get(v_a_4973_, 0);
                            lean_inc(v_mvarId_4975_);
                            lean_dec_ref_known(v_a_4973_, 3);
                            v___x_4976_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_4976_, 0, v___x_4913_);
                            lean_ctor_set(v___x_4976_, 1, v_mvarId_4975_);
                            v_a_4891_ = v___x_4976_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4913_);
                        v_a_4977_ = lean_ctor_get(v___x_4972_, 0);
                        lean_inc(v_a_4977_);
                        lean_dec_ref_known(v___x_4972_, 1);
                        v___x_4978_ = l_Lean_Exception_isInterrupt(v_a_4977_);
                        if v___x_4978_ == 0 {
                            lean_inc(v_a_4977_);
                            v___x_4979_ = l_Lean_Exception_isRuntime(v_a_4977_);
                            v___y_4937_ = v_a_4977_;
                            v___y_4938_ = v___x_4979_;
                            state = 13;
                            continue;
                        } else {
                            v___y_4937_ = v_a_4977_;
                            v___y_4938_ = v___x_4978_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4932_);
                    lean_del_object(v___x_4922_);
                    lean_dec(v___x_4913_);
                    lean_del_object(v___x_4887_);
                    lean_dec(v_val_4885_);
                    lean_dec(v_snd_4871_);
                    v_a_4877_ = v___x_4900_;
                    state = 2;
                    continue;
                }
            }
            19 => {
                if v_isShared_4986_ == 0 {
                    v___x_4988_ = v___x_4985_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4989_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_a_4983_);
                    v___x_4988_ = v_reuseFailAlloc_4989_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4988_;
            }
            21 => {
                if v_isShared_4994_ == 0 {
                    v___x_4996_ = v___x_4993_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4997_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_a_4991_);
                    v___x_4996_ = v_reuseFailAlloc_4997_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4996_;
            }
            23 => {
                if v_isShared_5002_ == 0 {
                    v___x_5004_ = v___x_5001_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
                    v___x_5004_ = v_reuseFailAlloc_5005_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5004_;
            }
            25 => {
                if v_isShared_5011_ == 0 {
                    v___x_5013_ = v___x_5010_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5014_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
                    v___x_5013_ = v_reuseFailAlloc_5014_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___boxed(
    mut v_forbidden_5019_: *mut LeanObject,
    mut v_mvarId_5020_: *mut LeanObject,
    mut v_as_5021_: *mut LeanObject,
    mut v_sz_5022_: *mut LeanObject,
    mut v_i_5023_: *mut LeanObject,
    mut v_b_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
    mut v___y_5026_: *mut LeanObject,
    mut v___y_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
    mut v___y_5029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5030_: usize = 0;
    let mut v_i_boxed_5031_: usize = 0;
    let mut v_res_5032_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5030_ = lean_unbox_usize(v_sz_5022_);
    lean_dec(v_sz_5022_);
    v_i_boxed_5031_ = lean_unbox_usize(v_i_5023_);
    lean_dec(v_i_5023_);
    v_res_5032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6(v_forbidden_5019_, v_mvarId_5020_, v_as_5021_, v_sz_boxed_5030_, v_i_boxed_5031_, v_b_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_);
    lean_dec(v___y_5028_);
    lean_dec_ref(v___y_5027_);
    lean_dec(v___y_5026_);
    lean_dec_ref(v___y_5025_);
    lean_dec_ref(v_as_5021_);
    lean_dec(v_forbidden_5019_);
    return v_res_5032_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5(
    mut v_forbidden_5033_: *mut LeanObject,
    mut v_mvarId_5034_: *mut LeanObject,
    mut v_as_5035_: *mut LeanObject,
    mut v_sz_5036_: usize,
    mut v_i_5037_: usize,
    mut v_b_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
    mut v___y_5042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5044_: u8 = 0;
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5049_: u8 = 0;
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: usize = 0;
    let mut v___x_5056_: usize = 0;
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5083_: u8 = 0;
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5087_: u8 = 0;
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: u8 = 0;
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5098_: u8 = 0;
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: u8 = 0;
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5108_: u8 = 0;
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5113_: u8 = 0;
    let mut v_options_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5115_: u8 = 0;
    let mut v_inheritedTraceOptions_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: u8 = 0;
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5135_: u8 = 0;
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5139_: u8 = 0;
    let mut v_reuseFailAlloc_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5145_: u8 = 0;
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: u8 = 0;
    let mut v___x_5154_: u8 = 0;
    let mut v___x_5155_: u8 = 0;
    let mut v___x_5156_: u8 = 0;
    let mut v_isSharedCheck_5157_: u8 = 0;
    let mut v_a_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5161_: u8 = 0;
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5165_: u8 = 0;
    let mut v_a_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5169_: u8 = 0;
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5173_: u8 = 0;
    let mut v_a_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5177_: u8 = 0;
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5181_: u8 = 0;
    let mut v_isSharedCheck_5182_: u8 = 0;
    let mut v_a_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5186_: u8 = 0;
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5190_: u8 = 0;
    let mut v_isSharedCheck_5191_: u8 = 0;
    let mut v_isSharedCheck_5192_: u8 = 0;
    let mut v_unused_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5044_ = lean_usize_dec_lt(v_i_5037_, v_sz_5036_);
                if v___x_5044_ == 0 {
                    lean_dec(v_mvarId_5034_);
                    v___x_5045_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5045_, 0, v_b_5038_);
                    return v___x_5045_;
                } else {
                    v_snd_5046_ = lean_ctor_get(v_b_5038_, 1);
                    v_isSharedCheck_5192_ = (!lean_is_exclusive(v_b_5038_)) as u8;
                    if v_isSharedCheck_5192_ == 0 {
                        v_unused_5193_ = lean_ctor_get(v_b_5038_, 0);
                        lean_dec(v_unused_5193_);
                        v___x_5048_ = v_b_5038_;
                        v_isShared_5049_ = v_isSharedCheck_5192_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5046_);
                        lean_dec(v_b_5038_);
                        v___x_5048_ = lean_box(0);
                        v_isShared_5049_ = v_isSharedCheck_5192_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5050_ = lean_box(0);
                v_a_5059_ = lean_array_uget(v_as_5035_, v_i_5037_);
                if lean_obj_tag(v_a_5059_) == 0 {
                    v_a_5052_ = v_snd_5046_;
                    state = 2;
                    continue;
                } else {
                    v_val_5060_ = lean_ctor_get(v_a_5059_, 0);
                    v_isSharedCheck_5191_ = (!lean_is_exclusive(v_a_5059_)) as u8;
                    if v_isSharedCheck_5191_ == 0 {
                        v___x_5062_ = v_a_5059_;
                        v_isShared_5063_ = v_isSharedCheck_5191_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_5060_);
                        lean_dec(v_a_5059_);
                        v___x_5062_ = lean_box(0);
                        v_isShared_5063_ = v_isSharedCheck_5191_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5049_ == 0 {
                    lean_ctor_set(v___x_5048_, 1, v_a_5052_);
                    lean_ctor_set(v___x_5048_, 0, v___x_5050_);
                    v___x_5054_ = v___x_5048_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5050_);
                    lean_ctor_set(v_reuseFailAlloc_5058_, 1, v_a_5052_);
                    v___x_5054_ = v_reuseFailAlloc_5058_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5055_ = 1usize;
                v___x_5056_ = lean_usize_add(v_i_5037_, v___x_5055_);
                v___x_5057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6(v_forbidden_5033_, v_mvarId_5034_, v_as_5035_, v_sz_5036_, v___x_5056_, v___x_5054_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
                return v___x_5057_;
            }
            4 => {
                v___x_5064_ = lean_box(0);
                v___x_5075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__0;
                v___x_5088_ = l_Lean_LocalDecl_fvarId(v_val_5060_);
                v___x_5089_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0___redArg(v___x_5088_, v_forbidden_5033_);
                if v___x_5089_ == 0 {
                    v___x_5090_ = l_Lean_LocalDecl_type(v_val_5060_);
                    v___x_5091_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAnyCandidate_x3f(v___x_5090_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
                    if lean_obj_tag(v___x_5091_) == 0 {
                        v_a_5092_ = lean_ctor_get(v___x_5091_, 0);
                        lean_inc(v_a_5092_);
                        lean_dec_ref_known(v___x_5091_, 1);
                        if lean_obj_tag(v_a_5092_) == 1 {
                            v_val_5093_ = lean_ctor_get(v_a_5092_, 0);
                            lean_inc(v_val_5093_);
                            lean_dec_ref_known(v_a_5092_, 1);
                            v_fst_5094_ = lean_ctor_get(v_val_5093_, 0);
                            v_snd_5095_ = lean_ctor_get(v_val_5093_, 1);
                            v_isSharedCheck_5182_ = (!lean_is_exclusive(v_val_5093_)) as u8;
                            if v_isSharedCheck_5182_ == 0 {
                                v___x_5097_ = v_val_5093_;
                                v_isShared_5098_ = v_isSharedCheck_5182_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_snd_5095_);
                                lean_inc(v_fst_5094_);
                                lean_dec(v_val_5093_);
                                v___x_5097_ = lean_box(0);
                                v_isShared_5098_ = v_isSharedCheck_5182_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5092_);
                            lean_dec(v___x_5088_);
                            lean_del_object(v___x_5062_);
                            lean_dec(v_val_5060_);
                            lean_dec(v_snd_5046_);
                            v_a_5052_ = v___x_5075_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5088_);
                        lean_del_object(v___x_5062_);
                        lean_dec(v_val_5060_);
                        lean_del_object(v___x_5048_);
                        lean_dec(v_snd_5046_);
                        lean_dec(v_mvarId_5034_);
                        v_a_5183_ = lean_ctor_get(v___x_5091_, 0);
                        v_isSharedCheck_5190_ = (!lean_is_exclusive(v___x_5091_)) as u8;
                        if v_isSharedCheck_5190_ == 0 {
                            v___x_5185_ = v___x_5091_;
                            v_isShared_5186_ = v_isSharedCheck_5190_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_5183_);
                            lean_dec(v___x_5091_);
                            v___x_5185_ = lean_box(0);
                            v_isShared_5186_ = v_isSharedCheck_5190_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_5088_);
                    lean_del_object(v___x_5062_);
                    lean_dec(v_val_5060_);
                    lean_dec(v_snd_5046_);
                    v_a_5052_ = v___x_5075_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_5063_ == 0 {
                    lean_ctor_set(v___x_5062_, 0, v_a_5066_);
                    v___x_5068_ = v___x_5062_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5066_);
                    v___x_5068_ = v_reuseFailAlloc_5074_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5069_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5069_, 0, v___x_5068_);
                lean_ctor_set(v___x_5069_, 1, v___x_5064_);
                v___x_5070_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5070_, 0, v___x_5069_);
                v___x_5071_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5071_, 0, v___x_5070_);
                v___x_5072_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5072_, 0, v___x_5071_);
                lean_ctor_set(v___x_5072_, 1, v_snd_5046_);
                v___x_5073_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5073_, 0, v___x_5072_);
                return v___x_5073_;
            }
            7 => {
                if lean_obj_tag(v___y_5077_) == 0 {
                    v_a_5078_ = lean_ctor_get(v___y_5077_, 0);
                    lean_inc(v_a_5078_);
                    lean_dec_ref_known(v___y_5077_, 1);
                    if lean_obj_tag(v_a_5078_) == 0 {
                        lean_del_object(v___x_5048_);
                        lean_dec(v_mvarId_5034_);
                        v_a_5079_ = lean_ctor_get(v_a_5078_, 0);
                        lean_inc(v_a_5079_);
                        lean_dec_ref_known(v_a_5078_, 1);
                        v_a_5066_ = v_a_5079_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec_ref_known(v_a_5078_, 1);
                        lean_del_object(v___x_5062_);
                        lean_dec(v_snd_5046_);
                        v_a_5052_ = v___x_5075_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5062_);
                    lean_del_object(v___x_5048_);
                    lean_dec(v_snd_5046_);
                    lean_dec(v_mvarId_5034_);
                    v_a_5080_ = lean_ctor_get(v___y_5077_, 0);
                    v_isSharedCheck_5087_ = (!lean_is_exclusive(v___y_5077_)) as u8;
                    if v_isSharedCheck_5087_ == 0 {
                        v___x_5082_ = v___y_5077_;
                        v_isShared_5083_ = v_isSharedCheck_5087_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5080_);
                        lean_dec(v___y_5077_);
                        v___x_5082_ = lean_box(0);
                        v_isShared_5083_ = v_isSharedCheck_5087_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5083_ == 0 {
                    v___x_5085_ = v___x_5082_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
                    v___x_5085_ = v_reuseFailAlloc_5086_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5085_;
            }
            10 => {
                lean_inc(v_snd_5095_);
                lean_inc(v_fst_5094_);
                v___x_5099_ = l_Lean_Meta_isExprDefEq(
                    v_fst_5094_,
                    v_snd_5095_,
                    v___y_5039_,
                    v___y_5040_,
                    v___y_5041_,
                    v___y_5042_,
                );
                if lean_obj_tag(v___x_5099_) == 0 {
                    v_a_5100_ = lean_ctor_get(v___x_5099_, 0);
                    lean_inc(v_a_5100_);
                    lean_dec_ref_known(v___x_5099_, 1);
                    v___x_5101_ = (lean_unbox(v_a_5100_) as u8);
                    lean_dec(v_a_5100_);
                    if v___x_5101_ == 0 {
                        lean_inc(v___y_5042_);
                        lean_inc_ref(v___y_5041_);
                        lean_inc(v___y_5040_);
                        lean_inc_ref(v___y_5039_);
                        v___x_5102_ = lean_whnf(
                            v_fst_5094_,
                            v___y_5039_,
                            v___y_5040_,
                            v___y_5041_,
                            v___y_5042_,
                        );
                        if lean_obj_tag(v___x_5102_) == 0 {
                            v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
                            lean_inc(v_a_5103_);
                            lean_dec_ref_known(v___x_5102_, 1);
                            lean_inc(v___y_5042_);
                            lean_inc_ref(v___y_5041_);
                            lean_inc(v___y_5040_);
                            lean_inc_ref(v___y_5039_);
                            v___x_5104_ = lean_whnf(
                                v_snd_5095_,
                                v___y_5039_,
                                v___y_5040_,
                                v___y_5041_,
                                v___y_5042_,
                            );
                            if lean_obj_tag(v___x_5104_) == 0 {
                                v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
                                v_isSharedCheck_5157_ = (!lean_is_exclusive(v___x_5104_)) as u8;
                                if v_isSharedCheck_5157_ == 0 {
                                    v___x_5107_ = v___x_5104_;
                                    v_isShared_5108_ = v_isSharedCheck_5157_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_5105_);
                                    lean_dec(v___x_5104_);
                                    v___x_5107_ = lean_box(0);
                                    v_isShared_5108_ = v_isSharedCheck_5157_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5103_);
                                lean_del_object(v___x_5097_);
                                lean_dec(v___x_5088_);
                                lean_del_object(v___x_5062_);
                                lean_dec(v_val_5060_);
                                lean_del_object(v___x_5048_);
                                lean_dec(v_snd_5046_);
                                lean_dec(v_mvarId_5034_);
                                v_a_5158_ = lean_ctor_get(v___x_5104_, 0);
                                v_isSharedCheck_5165_ = (!lean_is_exclusive(v___x_5104_)) as u8;
                                if v_isSharedCheck_5165_ == 0 {
                                    v___x_5160_ = v___x_5104_;
                                    v_isShared_5161_ = v_isSharedCheck_5165_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_5158_);
                                    lean_dec(v___x_5104_);
                                    v___x_5160_ = lean_box(0);
                                    v_isShared_5161_ = v_isSharedCheck_5165_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_5097_);
                            lean_dec(v_snd_5095_);
                            lean_dec(v___x_5088_);
                            lean_del_object(v___x_5062_);
                            lean_dec(v_val_5060_);
                            lean_del_object(v___x_5048_);
                            lean_dec(v_snd_5046_);
                            lean_dec(v_mvarId_5034_);
                            v_a_5166_ = lean_ctor_get(v___x_5102_, 0);
                            v_isSharedCheck_5173_ = (!lean_is_exclusive(v___x_5102_)) as u8;
                            if v_isSharedCheck_5173_ == 0 {
                                v___x_5168_ = v___x_5102_;
                                v_isShared_5169_ = v_isSharedCheck_5173_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_5166_);
                                lean_dec(v___x_5102_);
                                v___x_5168_ = lean_box(0);
                                v_isShared_5169_ = v_isSharedCheck_5173_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_5097_);
                        lean_dec(v_snd_5095_);
                        lean_dec(v_fst_5094_);
                        lean_dec(v___x_5088_);
                        lean_del_object(v___x_5062_);
                        lean_dec(v_val_5060_);
                        lean_dec(v_snd_5046_);
                        v_a_5052_ = v___x_5075_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5097_);
                    lean_dec(v_snd_5095_);
                    lean_dec(v_fst_5094_);
                    lean_dec(v___x_5088_);
                    lean_del_object(v___x_5062_);
                    lean_dec(v_val_5060_);
                    lean_del_object(v___x_5048_);
                    lean_dec(v_snd_5046_);
                    lean_dec(v_mvarId_5034_);
                    v_a_5174_ = lean_ctor_get(v___x_5099_, 0);
                    v_isSharedCheck_5181_ = (!lean_is_exclusive(v___x_5099_)) as u8;
                    if v_isSharedCheck_5181_ == 0 {
                        v___x_5176_ = v___x_5099_;
                        v_isShared_5177_ = v_isSharedCheck_5181_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_5174_);
                        lean_dec(v___x_5099_);
                        v___x_5176_ = lean_box(0);
                        v_isShared_5177_ = v_isSharedCheck_5181_;
                        state = 23;
                        continue;
                    }
                }
            }
            11 => {
                v___x_5155_ = l_Lean_Expr_isRawNatLit(v_a_5103_);
                lean_dec(v_a_5103_);
                if v___x_5155_ == 0 {
                    lean_dec(v_a_5105_);
                    v___y_5145_ = v___x_5155_;
                    state = 18;
                    continue;
                } else {
                    v___x_5156_ = l_Lean_Expr_isRawNatLit(v_a_5105_);
                    lean_dec(v_a_5105_);
                    v___y_5145_ = v___x_5156_;
                    state = 18;
                    continue;
                }
            }
            12 => {
                v___x_5110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0(v___x_5064_, v___x_5064_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
                v___y_5077_ = v___x_5110_;
                state = 7;
                continue;
            }
            13 => {
                if v___y_5113_ == 0 {
                    lean_del_object(v___x_5107_);
                    v_options_5114_ = lean_ctor_get(v___y_5041_, 2);
                    v_hasTrace_5115_ = lean_ctor_get_uint8(
                        v_options_5114_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5115_ == 0 {
                        lean_dec_ref(v___y_5112_);
                        lean_del_object(v___x_5097_);
                        lean_dec(v_val_5060_);
                        state = 12;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5116_ = lean_ctor_get(v___y_5041_, 13);
                        v___x_5117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4;
                        v___x_5118_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7);
                        v___x_5119_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5116_,
                            v_options_5114_,
                            v___x_5118_,
                        );
                        if v___x_5119_ == 0 {
                            lean_dec_ref(v___y_5112_);
                            lean_del_object(v___x_5097_);
                            lean_dec(v_val_5060_);
                            state = 12;
                            continue;
                        } else {
                            v___x_5120_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9);
                            v___x_5121_ = l_Lean_LocalDecl_userName(v_val_5060_);
                            lean_dec(v_val_5060_);
                            v___x_5122_ = l_Lean_MessageData_ofName(v___x_5121_);
                            if v_isShared_5098_ == 0 {
                                lean_ctor_set_tag(v___x_5097_, 7);
                                lean_ctor_set(v___x_5097_, 1, v___x_5122_);
                                lean_ctor_set(v___x_5097_, 0, v___x_5120_);
                                v___x_5124_ = v___x_5097_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_5140_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5140_, 0, v___x_5120_);
                                lean_ctor_set(v_reuseFailAlloc_5140_, 1, v___x_5122_);
                                v___x_5124_ = v_reuseFailAlloc_5140_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5097_);
                    lean_del_object(v___x_5062_);
                    lean_dec(v_val_5060_);
                    lean_del_object(v___x_5048_);
                    lean_dec(v_snd_5046_);
                    lean_dec(v_mvarId_5034_);
                    if v_isShared_5108_ == 0 {
                        lean_ctor_set_tag(v___x_5107_, 1);
                        lean_ctor_set(v___x_5107_, 0, v___y_5112_);
                        v___x_5142_ = v___x_5107_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_5143_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5143_, 0, v___y_5112_);
                        v___x_5142_ = v_reuseFailAlloc_5143_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                v___x_5125_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11);
                v___x_5126_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5126_, 0, v___x_5124_);
                lean_ctor_set(v___x_5126_, 1, v___x_5125_);
                v___x_5127_ = l_Lean_Exception_toMessageData(v___y_5112_);
                v___x_5128_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5128_, 0, v___x_5126_);
                lean_ctor_set(v___x_5128_, 1, v___x_5127_);
                v___x_5129_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1(v___x_5117_, v___x_5128_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
                if lean_obj_tag(v___x_5129_) == 0 {
                    v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
                    lean_inc(v_a_5130_);
                    lean_dec_ref_known(v___x_5129_, 1);
                    v___x_5131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0(v___x_5064_, v_a_5130_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
                    v___y_5077_ = v___x_5131_;
                    state = 7;
                    continue;
                } else {
                    lean_del_object(v___x_5062_);
                    lean_del_object(v___x_5048_);
                    lean_dec(v_snd_5046_);
                    lean_dec(v_mvarId_5034_);
                    v_a_5132_ = lean_ctor_get(v___x_5129_, 0);
                    v_isSharedCheck_5139_ = (!lean_is_exclusive(v___x_5129_)) as u8;
                    if v_isSharedCheck_5139_ == 0 {
                        v___x_5134_ = v___x_5129_;
                        v_isShared_5135_ = v_isSharedCheck_5139_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_5132_);
                        lean_dec(v___x_5129_);
                        v___x_5134_ = lean_box(0);
                        v_isShared_5135_ = v_isSharedCheck_5139_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_5135_ == 0 {
                    v___x_5137_ = v___x_5134_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5132_);
                    v___x_5137_ = v_reuseFailAlloc_5138_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5137_;
            }
            17 => {
                return v___x_5142_;
            }
            18 => {
                if v___y_5145_ == 0 {
                    v___x_5146_ = lean_box(0);
                    lean_inc(v___x_5088_);
                    lean_inc(v_mvarId_5034_);
                    v___x_5147_ = l_Lean_Meta_injection(
                        v_mvarId_5034_,
                        v___x_5088_,
                        v___x_5146_,
                        v___y_5039_,
                        v___y_5040_,
                        v___y_5041_,
                        v___y_5042_,
                    );
                    if lean_obj_tag(v___x_5147_) == 0 {
                        lean_del_object(v___x_5107_);
                        lean_del_object(v___x_5097_);
                        lean_dec(v_val_5060_);
                        lean_del_object(v___x_5048_);
                        lean_dec(v_mvarId_5034_);
                        v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
                        lean_inc(v_a_5148_);
                        lean_dec_ref_known(v___x_5147_, 1);
                        if lean_obj_tag(v_a_5148_) == 0 {
                            lean_dec(v___x_5088_);
                            v___x_5149_ = lean_box(0);
                            v_a_5066_ = v___x_5149_;
                            state = 5;
                            continue;
                        } else {
                            v_mvarId_5150_ = lean_ctor_get(v_a_5148_, 0);
                            lean_inc(v_mvarId_5150_);
                            lean_dec_ref_known(v_a_5148_, 3);
                            v___x_5151_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_5151_, 0, v___x_5088_);
                            lean_ctor_set(v___x_5151_, 1, v_mvarId_5150_);
                            v_a_5066_ = v___x_5151_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5088_);
                        v_a_5152_ = lean_ctor_get(v___x_5147_, 0);
                        lean_inc(v_a_5152_);
                        lean_dec_ref_known(v___x_5147_, 1);
                        v___x_5153_ = l_Lean_Exception_isInterrupt(v_a_5152_);
                        if v___x_5153_ == 0 {
                            lean_inc(v_a_5152_);
                            v___x_5154_ = l_Lean_Exception_isRuntime(v_a_5152_);
                            v___y_5112_ = v_a_5152_;
                            v___y_5113_ = v___x_5154_;
                            state = 13;
                            continue;
                        } else {
                            v___y_5112_ = v_a_5152_;
                            v___y_5113_ = v___x_5153_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5107_);
                    lean_del_object(v___x_5097_);
                    lean_dec(v___x_5088_);
                    lean_del_object(v___x_5062_);
                    lean_dec(v_val_5060_);
                    lean_dec(v_snd_5046_);
                    v_a_5052_ = v___x_5075_;
                    state = 2;
                    continue;
                }
            }
            19 => {
                if v_isShared_5161_ == 0 {
                    v___x_5163_ = v___x_5160_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5164_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5164_, 0, v_a_5158_);
                    v___x_5163_ = v_reuseFailAlloc_5164_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5163_;
            }
            21 => {
                if v_isShared_5169_ == 0 {
                    v___x_5171_ = v___x_5168_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_a_5166_);
                    v___x_5171_ = v_reuseFailAlloc_5172_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5171_;
            }
            23 => {
                if v_isShared_5177_ == 0 {
                    v___x_5179_ = v___x_5176_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5180_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_a_5174_);
                    v___x_5179_ = v_reuseFailAlloc_5180_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5179_;
            }
            25 => {
                if v_isShared_5186_ == 0 {
                    v___x_5188_ = v___x_5185_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_a_5183_);
                    v___x_5188_ = v_reuseFailAlloc_5189_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5___boxed(
    mut v_forbidden_5194_: *mut LeanObject,
    mut v_mvarId_5195_: *mut LeanObject,
    mut v_as_5196_: *mut LeanObject,
    mut v_sz_5197_: *mut LeanObject,
    mut v_i_5198_: *mut LeanObject,
    mut v_b_5199_: *mut LeanObject,
    mut v___y_5200_: *mut LeanObject,
    mut v___y_5201_: *mut LeanObject,
    mut v___y_5202_: *mut LeanObject,
    mut v___y_5203_: *mut LeanObject,
    mut v___y_5204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5205_: usize = 0;
    let mut v_i_boxed_5206_: usize = 0;
    let mut v_res_5207_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5205_ = lean_unbox_usize(v_sz_5197_);
    lean_dec(v_sz_5197_);
    v_i_boxed_5206_ = lean_unbox_usize(v_i_5198_);
    lean_dec(v_i_5198_);
    v_res_5207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5(v_forbidden_5194_, v_mvarId_5195_, v_as_5196_, v_sz_boxed_5205_, v_i_boxed_5206_, v_b_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_);
    lean_dec(v___y_5203_);
    lean_dec_ref(v___y_5202_);
    lean_dec(v___y_5201_);
    lean_dec_ref(v___y_5200_);
    lean_dec_ref(v_as_5196_);
    lean_dec(v_forbidden_5194_);
    return v_res_5207_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3(
    mut v_init_5208_: *mut LeanObject,
    mut v_forbidden_5209_: *mut LeanObject,
    mut v_mvarId_5210_: *mut LeanObject,
    mut v_n_5211_: *mut LeanObject,
    mut v_b_5212_: *mut LeanObject,
    mut v___y_5213_: *mut LeanObject,
    mut v___y_5214_: *mut LeanObject,
    mut v___y_5215_: *mut LeanObject,
    mut v___y_5216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5221_: usize = 0;
    let mut v___x_5222_: usize = 0;
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5227_: u8 = 0;
    let mut v_fst_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5238_: u8 = 0;
    let mut v_a_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5242_: u8 = 0;
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5246_: u8 = 0;
    let mut v_vs_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5250_: usize = 0;
    let mut v___x_5251_: usize = 0;
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5256_: u8 = 0;
    let mut v_fst_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut v_a_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5271_: u8 = 0;
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_5211_) == 0 {
                    v_cs_5218_ = lean_ctor_get(v_n_5211_, 0);
                    v___x_5219_ = lean_box(0);
                    v___x_5220_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5220_, 0, v___x_5219_);
                    lean_ctor_set(v___x_5220_, 1, v_b_5212_);
                    v_sz_5221_ = lean_array_size(v_cs_5218_);
                    v___x_5222_ = 0usize;
                    v___x_5223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__4(v_init_5208_, v_forbidden_5209_, v_mvarId_5210_, v_cs_5218_, v_sz_5221_, v___x_5222_, v___x_5220_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_);
                    if lean_obj_tag(v___x_5223_) == 0 {
                        v_a_5224_ = lean_ctor_get(v___x_5223_, 0);
                        v_isSharedCheck_5238_ = (!lean_is_exclusive(v___x_5223_)) as u8;
                        if v_isSharedCheck_5238_ == 0 {
                            v___x_5226_ = v___x_5223_;
                            v_isShared_5227_ = v_isSharedCheck_5238_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5224_);
                            lean_dec(v___x_5223_);
                            v___x_5226_ = lean_box(0);
                            v_isShared_5227_ = v_isSharedCheck_5238_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5239_ = lean_ctor_get(v___x_5223_, 0);
                        v_isSharedCheck_5246_ = (!lean_is_exclusive(v___x_5223_)) as u8;
                        if v_isSharedCheck_5246_ == 0 {
                            v___x_5241_ = v___x_5223_;
                            v_isShared_5242_ = v_isSharedCheck_5246_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5239_);
                            lean_dec(v___x_5223_);
                            v___x_5241_ = lean_box(0);
                            v_isShared_5242_ = v_isSharedCheck_5246_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5247_ = lean_ctor_get(v_n_5211_, 0);
                    v___x_5248_ = lean_box(0);
                    v___x_5249_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5249_, 0, v___x_5248_);
                    lean_ctor_set(v___x_5249_, 1, v_b_5212_);
                    v_sz_5250_ = lean_array_size(v_vs_5247_);
                    v___x_5251_ = 0usize;
                    v___x_5252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5(v_forbidden_5209_, v_mvarId_5210_, v_vs_5247_, v_sz_5250_, v___x_5251_, v___x_5249_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_);
                    if lean_obj_tag(v___x_5252_) == 0 {
                        v_a_5253_ = lean_ctor_get(v___x_5252_, 0);
                        v_isSharedCheck_5267_ = (!lean_is_exclusive(v___x_5252_)) as u8;
                        if v_isSharedCheck_5267_ == 0 {
                            v___x_5255_ = v___x_5252_;
                            v_isShared_5256_ = v_isSharedCheck_5267_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5253_);
                            lean_dec(v___x_5252_);
                            v___x_5255_ = lean_box(0);
                            v_isShared_5256_ = v_isSharedCheck_5267_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5268_ = lean_ctor_get(v___x_5252_, 0);
                        v_isSharedCheck_5275_ = (!lean_is_exclusive(v___x_5252_)) as u8;
                        if v_isSharedCheck_5275_ == 0 {
                            v___x_5270_ = v___x_5252_;
                            v_isShared_5271_ = v_isSharedCheck_5275_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5268_);
                            lean_dec(v___x_5252_);
                            v___x_5270_ = lean_box(0);
                            v_isShared_5271_ = v_isSharedCheck_5275_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5228_ = lean_ctor_get(v_a_5224_, 0);
                if lean_obj_tag(v_fst_5228_) == 0 {
                    v_snd_5229_ = lean_ctor_get(v_a_5224_, 1);
                    lean_inc(v_snd_5229_);
                    lean_dec(v_a_5224_);
                    v___x_5230_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5230_, 0, v_snd_5229_);
                    if v_isShared_5227_ == 0 {
                        lean_ctor_set(v___x_5226_, 0, v___x_5230_);
                        v___x_5232_ = v___x_5226_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5233_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5233_, 0, v___x_5230_);
                        v___x_5232_ = v_reuseFailAlloc_5233_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5228_);
                    lean_dec(v_a_5224_);
                    v_val_5234_ = lean_ctor_get(v_fst_5228_, 0);
                    lean_inc(v_val_5234_);
                    lean_dec_ref_known(v_fst_5228_, 1);
                    if v_isShared_5227_ == 0 {
                        lean_ctor_set(v___x_5226_, 0, v_val_5234_);
                        v___x_5236_ = v___x_5226_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5237_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5237_, 0, v_val_5234_);
                        v___x_5236_ = v_reuseFailAlloc_5237_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5232_;
            }
            3 => {
                return v___x_5236_;
            }
            4 => {
                if v_isShared_5242_ == 0 {
                    v___x_5244_ = v___x_5241_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
                    v___x_5244_ = v_reuseFailAlloc_5245_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5244_;
            }
            6 => {
                v_fst_5257_ = lean_ctor_get(v_a_5253_, 0);
                if lean_obj_tag(v_fst_5257_) == 0 {
                    v_snd_5258_ = lean_ctor_get(v_a_5253_, 1);
                    lean_inc(v_snd_5258_);
                    lean_dec(v_a_5253_);
                    v___x_5259_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5259_, 0, v_snd_5258_);
                    if v_isShared_5256_ == 0 {
                        lean_ctor_set(v___x_5255_, 0, v___x_5259_);
                        v___x_5261_ = v___x_5255_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5262_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5262_, 0, v___x_5259_);
                        v___x_5261_ = v_reuseFailAlloc_5262_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5257_);
                    lean_dec(v_a_5253_);
                    v_val_5263_ = lean_ctor_get(v_fst_5257_, 0);
                    lean_inc(v_val_5263_);
                    lean_dec_ref_known(v_fst_5257_, 1);
                    if v_isShared_5256_ == 0 {
                        lean_ctor_set(v___x_5255_, 0, v_val_5263_);
                        v___x_5265_ = v___x_5255_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_val_5263_);
                        v___x_5265_ = v_reuseFailAlloc_5266_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5261_;
            }
            8 => {
                return v___x_5265_;
            }
            9 => {
                if v_isShared_5271_ == 0 {
                    v___x_5273_ = v___x_5270_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
                    v___x_5273_ = v_reuseFailAlloc_5274_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__4(
    mut v_init_5276_: *mut LeanObject,
    mut v_forbidden_5277_: *mut LeanObject,
    mut v_mvarId_5278_: *mut LeanObject,
    mut v_as_5279_: *mut LeanObject,
    mut v_sz_5280_: usize,
    mut v_i_5281_: usize,
    mut v_b_5282_: *mut LeanObject,
    mut v___y_5283_: *mut LeanObject,
    mut v___y_5284_: *mut LeanObject,
    mut v___y_5285_: *mut LeanObject,
    mut v___y_5286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5288_: u8 = 0;
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v_a_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5299_: u8 = 0;
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: usize = 0;
    let mut v___x_5312_: usize = 0;
    let mut v_reuseFailAlloc_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5315_: u8 = 0;
    let mut v_a_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5319_: u8 = 0;
    let mut v___x_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5323_: u8 = 0;
    let mut v_isSharedCheck_5324_: u8 = 0;
    let mut v_unused_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5288_ = lean_usize_dec_lt(v_i_5281_, v_sz_5280_);
                if v___x_5288_ == 0 {
                    lean_dec(v_mvarId_5278_);
                    v___x_5289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5289_, 0, v_b_5282_);
                    return v___x_5289_;
                } else {
                    v_snd_5290_ = lean_ctor_get(v_b_5282_, 1);
                    v_isSharedCheck_5324_ = (!lean_is_exclusive(v_b_5282_)) as u8;
                    if v_isSharedCheck_5324_ == 0 {
                        v_unused_5325_ = lean_ctor_get(v_b_5282_, 0);
                        lean_dec(v_unused_5325_);
                        v___x_5292_ = v_b_5282_;
                        v_isShared_5293_ = v_isSharedCheck_5324_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5290_);
                        lean_dec(v_b_5282_);
                        v___x_5292_ = lean_box(0);
                        v_isShared_5293_ = v_isSharedCheck_5324_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5294_ = lean_array_uget_borrowed(v_as_5279_, v_i_5281_);
                lean_inc(v_snd_5290_);
                lean_inc(v_mvarId_5278_);
                v___x_5295_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3(v_init_5276_, v_forbidden_5277_, v_mvarId_5278_, v_a_5294_, v_snd_5290_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
                if lean_obj_tag(v___x_5295_) == 0 {
                    v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
                    v_isSharedCheck_5315_ = (!lean_is_exclusive(v___x_5295_)) as u8;
                    if v_isSharedCheck_5315_ == 0 {
                        v___x_5298_ = v___x_5295_;
                        v_isShared_5299_ = v_isSharedCheck_5315_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5296_);
                        lean_dec(v___x_5295_);
                        v___x_5298_ = lean_box(0);
                        v_isShared_5299_ = v_isSharedCheck_5315_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5292_);
                    lean_dec(v_snd_5290_);
                    lean_dec(v_mvarId_5278_);
                    v_a_5316_ = lean_ctor_get(v___x_5295_, 0);
                    v_isSharedCheck_5323_ = (!lean_is_exclusive(v___x_5295_)) as u8;
                    if v_isSharedCheck_5323_ == 0 {
                        v___x_5318_ = v___x_5295_;
                        v_isShared_5319_ = v_isSharedCheck_5323_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5316_);
                        lean_dec(v___x_5295_);
                        v___x_5318_ = lean_box(0);
                        v_isShared_5319_ = v_isSharedCheck_5323_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_5296_) == 0 {
                    lean_dec(v_mvarId_5278_);
                    v___x_5300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5300_, 0, v_a_5296_);
                    if v_isShared_5293_ == 0 {
                        lean_ctor_set(v___x_5292_, 0, v___x_5300_);
                        v___x_5302_ = v___x_5292_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5306_, 0, v___x_5300_);
                        lean_ctor_set(v_reuseFailAlloc_5306_, 1, v_snd_5290_);
                        v___x_5302_ = v_reuseFailAlloc_5306_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5298_);
                    lean_dec(v_snd_5290_);
                    v_a_5307_ = lean_ctor_get(v_a_5296_, 0);
                    lean_inc(v_a_5307_);
                    lean_dec_ref_known(v_a_5296_, 1);
                    v___x_5308_ = lean_box(0);
                    if v_isShared_5293_ == 0 {
                        lean_ctor_set(v___x_5292_, 1, v_a_5307_);
                        lean_ctor_set(v___x_5292_, 0, v___x_5308_);
                        v___x_5310_ = v___x_5292_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5314_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5314_, 0, v___x_5308_);
                        lean_ctor_set(v_reuseFailAlloc_5314_, 1, v_a_5307_);
                        v___x_5310_ = v_reuseFailAlloc_5314_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5299_ == 0 {
                    lean_ctor_set(v___x_5298_, 0, v___x_5302_);
                    v___x_5304_ = v___x_5298_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5305_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5305_, 0, v___x_5302_);
                    v___x_5304_ = v_reuseFailAlloc_5305_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5304_;
            }
            5 => {
                v___x_5311_ = 1usize;
                v___x_5312_ = lean_usize_add(v_i_5281_, v___x_5311_);
                v_i_5281_ = v___x_5312_;
                v_b_5282_ = v___x_5310_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5319_ == 0 {
                    v___x_5321_ = v___x_5318_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
                    v___x_5321_ = v_reuseFailAlloc_5322_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__4___boxed(
    mut v_init_5326_: *mut LeanObject,
    mut v_forbidden_5327_: *mut LeanObject,
    mut v_mvarId_5328_: *mut LeanObject,
    mut v_as_5329_: *mut LeanObject,
    mut v_sz_5330_: *mut LeanObject,
    mut v_i_5331_: *mut LeanObject,
    mut v_b_5332_: *mut LeanObject,
    mut v___y_5333_: *mut LeanObject,
    mut v___y_5334_: *mut LeanObject,
    mut v___y_5335_: *mut LeanObject,
    mut v___y_5336_: *mut LeanObject,
    mut v___y_5337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5338_: usize = 0;
    let mut v_i_boxed_5339_: usize = 0;
    let mut v_res_5340_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5338_ = lean_unbox_usize(v_sz_5330_);
    lean_dec(v_sz_5330_);
    v_i_boxed_5339_ = lean_unbox_usize(v_i_5331_);
    lean_dec(v_i_5331_);
    v_res_5340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__4(v_init_5326_, v_forbidden_5327_, v_mvarId_5328_, v_as_5329_, v_sz_boxed_5338_, v_i_boxed_5339_, v_b_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_);
    lean_dec(v___y_5336_);
    lean_dec_ref(v___y_5335_);
    lean_dec(v___y_5334_);
    lean_dec_ref(v___y_5333_);
    lean_dec_ref(v_as_5329_);
    lean_dec(v_forbidden_5327_);
    lean_dec_ref(v_init_5326_);
    return v_res_5340_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3___boxed(
    mut v_init_5341_: *mut LeanObject,
    mut v_forbidden_5342_: *mut LeanObject,
    mut v_mvarId_5343_: *mut LeanObject,
    mut v_n_5344_: *mut LeanObject,
    mut v_b_5345_: *mut LeanObject,
    mut v___y_5346_: *mut LeanObject,
    mut v___y_5347_: *mut LeanObject,
    mut v___y_5348_: *mut LeanObject,
    mut v___y_5349_: *mut LeanObject,
    mut v___y_5350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5351_: *mut LeanObject = core::ptr::null_mut();
    v_res_5351_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3(v_init_5341_, v_forbidden_5342_, v_mvarId_5343_, v_n_5344_, v_b_5345_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
    lean_dec(v___y_5349_);
    lean_dec_ref(v___y_5348_);
    lean_dec(v___y_5347_);
    lean_dec_ref(v___y_5346_);
    lean_dec_ref(v_n_5344_);
    lean_dec(v_forbidden_5342_);
    lean_dec_ref(v_init_5341_);
    return v_res_5351_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4_spec__7(
    mut v_forbidden_5355_: *mut LeanObject,
    mut v_mvarId_5356_: *mut LeanObject,
    mut v_as_5357_: *mut LeanObject,
    mut v_sz_5358_: usize,
    mut v_i_5359_: usize,
    mut v_b_5360_: *mut LeanObject,
    mut v___y_5361_: *mut LeanObject,
    mut v___y_5362_: *mut LeanObject,
    mut v___y_5363_: *mut LeanObject,
    mut v___y_5364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5366_: u8 = 0;
    let mut v___x_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5371_: u8 = 0;
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: usize = 0;
    let mut v___x_5378_: usize = 0;
    let mut v_reuseFailAlloc_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5385_: u8 = 0;
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: u8 = 0;
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5419_: u8 = 0;
    let mut v___x_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: u8 = 0;
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5429_: u8 = 0;
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5434_: u8 = 0;
    let mut v_options_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5436_: u8 = 0;
    let mut v_inheritedTraceOptions_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: u8 = 0;
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5456_: u8 = 0;
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5460_: u8 = 0;
    let mut v_reuseFailAlloc_5461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5466_: u8 = 0;
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: u8 = 0;
    let mut v___x_5475_: u8 = 0;
    let mut v___x_5476_: u8 = 0;
    let mut v___x_5477_: u8 = 0;
    let mut v_isSharedCheck_5478_: u8 = 0;
    let mut v_a_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5482_: u8 = 0;
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5486_: u8 = 0;
    let mut v_a_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5490_: u8 = 0;
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5494_: u8 = 0;
    let mut v_a_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5498_: u8 = 0;
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5502_: u8 = 0;
    let mut v_isSharedCheck_5503_: u8 = 0;
    let mut v_a_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5507_: u8 = 0;
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5511_: u8 = 0;
    let mut v_isSharedCheck_5512_: u8 = 0;
    let mut v_isSharedCheck_5513_: u8 = 0;
    let mut v_unused_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5366_ = lean_usize_dec_lt(v_i_5359_, v_sz_5358_);
                if v___x_5366_ == 0 {
                    lean_dec(v_mvarId_5356_);
                    v___x_5367_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5367_, 0, v_b_5360_);
                    return v___x_5367_;
                } else {
                    v_snd_5368_ = lean_ctor_get(v_b_5360_, 1);
                    v_isSharedCheck_5513_ = (!lean_is_exclusive(v_b_5360_)) as u8;
                    if v_isSharedCheck_5513_ == 0 {
                        v_unused_5514_ = lean_ctor_get(v_b_5360_, 0);
                        lean_dec(v_unused_5514_);
                        v___x_5370_ = v_b_5360_;
                        v_isShared_5371_ = v_isSharedCheck_5513_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5368_);
                        lean_dec(v_b_5360_);
                        v___x_5370_ = lean_box(0);
                        v_isShared_5371_ = v_isSharedCheck_5513_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5372_ = lean_box(0);
                v_a_5381_ = lean_array_uget(v_as_5357_, v_i_5359_);
                if lean_obj_tag(v_a_5381_) == 0 {
                    v_a_5374_ = v_snd_5368_;
                    state = 2;
                    continue;
                } else {
                    v_val_5382_ = lean_ctor_get(v_a_5381_, 0);
                    v_isSharedCheck_5512_ = (!lean_is_exclusive(v_a_5381_)) as u8;
                    if v_isSharedCheck_5512_ == 0 {
                        v___x_5384_ = v_a_5381_;
                        v_isShared_5385_ = v_isSharedCheck_5512_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_5382_);
                        lean_dec(v_a_5381_);
                        v___x_5384_ = lean_box(0);
                        v_isShared_5385_ = v_isSharedCheck_5512_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5371_ == 0 {
                    lean_ctor_set(v___x_5370_, 1, v_a_5374_);
                    lean_ctor_set(v___x_5370_, 0, v___x_5372_);
                    v___x_5376_ = v___x_5370_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5372_);
                    lean_ctor_set(v_reuseFailAlloc_5380_, 1, v_a_5374_);
                    v___x_5376_ = v_reuseFailAlloc_5380_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5377_ = 1usize;
                v___x_5378_ = lean_usize_add(v_i_5359_, v___x_5377_);
                v_i_5359_ = v___x_5378_;
                v_b_5360_ = v___x_5376_;
                state = 0;
                continue;
            }
            4 => {
                v___x_5386_ = lean_box(0);
                v___x_5396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4_spec__7___closed__0;
                v___x_5409_ = l_Lean_LocalDecl_fvarId(v_val_5382_);
                v___x_5410_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0___redArg(v___x_5409_, v_forbidden_5355_);
                if v___x_5410_ == 0 {
                    v___x_5411_ = l_Lean_LocalDecl_type(v_val_5382_);
                    v___x_5412_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAnyCandidate_x3f(v___x_5411_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
                    if lean_obj_tag(v___x_5412_) == 0 {
                        v_a_5413_ = lean_ctor_get(v___x_5412_, 0);
                        lean_inc(v_a_5413_);
                        lean_dec_ref_known(v___x_5412_, 1);
                        if lean_obj_tag(v_a_5413_) == 1 {
                            v_val_5414_ = lean_ctor_get(v_a_5413_, 0);
                            lean_inc(v_val_5414_);
                            lean_dec_ref_known(v_a_5413_, 1);
                            v_fst_5415_ = lean_ctor_get(v_val_5414_, 0);
                            v_snd_5416_ = lean_ctor_get(v_val_5414_, 1);
                            v_isSharedCheck_5503_ = (!lean_is_exclusive(v_val_5414_)) as u8;
                            if v_isSharedCheck_5503_ == 0 {
                                v___x_5418_ = v_val_5414_;
                                v_isShared_5419_ = v_isSharedCheck_5503_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_snd_5416_);
                                lean_inc(v_fst_5415_);
                                lean_dec(v_val_5414_);
                                v___x_5418_ = lean_box(0);
                                v_isShared_5419_ = v_isSharedCheck_5503_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5413_);
                            lean_dec(v___x_5409_);
                            lean_del_object(v___x_5384_);
                            lean_dec(v_val_5382_);
                            lean_dec(v_snd_5368_);
                            v_a_5374_ = v___x_5396_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5409_);
                        lean_del_object(v___x_5384_);
                        lean_dec(v_val_5382_);
                        lean_del_object(v___x_5370_);
                        lean_dec(v_snd_5368_);
                        lean_dec(v_mvarId_5356_);
                        v_a_5504_ = lean_ctor_get(v___x_5412_, 0);
                        v_isSharedCheck_5511_ = (!lean_is_exclusive(v___x_5412_)) as u8;
                        if v_isSharedCheck_5511_ == 0 {
                            v___x_5506_ = v___x_5412_;
                            v_isShared_5507_ = v_isSharedCheck_5511_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_5504_);
                            lean_dec(v___x_5412_);
                            v___x_5506_ = lean_box(0);
                            v_isShared_5507_ = v_isSharedCheck_5511_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_5409_);
                    lean_del_object(v___x_5384_);
                    lean_dec(v_val_5382_);
                    lean_dec(v_snd_5368_);
                    v_a_5374_ = v___x_5396_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_5385_ == 0 {
                    lean_ctor_set(v___x_5384_, 0, v_a_5388_);
                    v___x_5390_ = v___x_5384_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5388_);
                    v___x_5390_ = v_reuseFailAlloc_5395_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5391_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5391_, 0, v___x_5390_);
                lean_ctor_set(v___x_5391_, 1, v___x_5386_);
                v___x_5392_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5392_, 0, v___x_5391_);
                v___x_5393_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5393_, 0, v___x_5392_);
                lean_ctor_set(v___x_5393_, 1, v_snd_5368_);
                v___x_5394_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5394_, 0, v___x_5393_);
                return v___x_5394_;
            }
            7 => {
                if lean_obj_tag(v___y_5398_) == 0 {
                    v_a_5399_ = lean_ctor_get(v___y_5398_, 0);
                    lean_inc(v_a_5399_);
                    lean_dec_ref_known(v___y_5398_, 1);
                    if lean_obj_tag(v_a_5399_) == 0 {
                        lean_del_object(v___x_5370_);
                        lean_dec(v_mvarId_5356_);
                        v_a_5400_ = lean_ctor_get(v_a_5399_, 0);
                        lean_inc(v_a_5400_);
                        lean_dec_ref_known(v_a_5399_, 1);
                        v_a_5388_ = v_a_5400_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec_ref_known(v_a_5399_, 1);
                        lean_del_object(v___x_5384_);
                        lean_dec(v_snd_5368_);
                        v_a_5374_ = v___x_5396_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5384_);
                    lean_del_object(v___x_5370_);
                    lean_dec(v_snd_5368_);
                    lean_dec(v_mvarId_5356_);
                    v_a_5401_ = lean_ctor_get(v___y_5398_, 0);
                    v_isSharedCheck_5408_ = (!lean_is_exclusive(v___y_5398_)) as u8;
                    if v_isSharedCheck_5408_ == 0 {
                        v___x_5403_ = v___y_5398_;
                        v_isShared_5404_ = v_isSharedCheck_5408_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5401_);
                        lean_dec(v___y_5398_);
                        v___x_5403_ = lean_box(0);
                        v_isShared_5404_ = v_isSharedCheck_5408_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5404_ == 0 {
                    v___x_5406_ = v___x_5403_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5407_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
                    v___x_5406_ = v_reuseFailAlloc_5407_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5406_;
            }
            10 => {
                lean_inc(v_snd_5416_);
                lean_inc(v_fst_5415_);
                v___x_5420_ = l_Lean_Meta_isExprDefEq(
                    v_fst_5415_,
                    v_snd_5416_,
                    v___y_5361_,
                    v___y_5362_,
                    v___y_5363_,
                    v___y_5364_,
                );
                if lean_obj_tag(v___x_5420_) == 0 {
                    v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
                    lean_inc(v_a_5421_);
                    lean_dec_ref_known(v___x_5420_, 1);
                    v___x_5422_ = (lean_unbox(v_a_5421_) as u8);
                    lean_dec(v_a_5421_);
                    if v___x_5422_ == 0 {
                        lean_inc(v___y_5364_);
                        lean_inc_ref(v___y_5363_);
                        lean_inc(v___y_5362_);
                        lean_inc_ref(v___y_5361_);
                        v___x_5423_ = lean_whnf(
                            v_fst_5415_,
                            v___y_5361_,
                            v___y_5362_,
                            v___y_5363_,
                            v___y_5364_,
                        );
                        if lean_obj_tag(v___x_5423_) == 0 {
                            v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
                            lean_inc(v_a_5424_);
                            lean_dec_ref_known(v___x_5423_, 1);
                            lean_inc(v___y_5364_);
                            lean_inc_ref(v___y_5363_);
                            lean_inc(v___y_5362_);
                            lean_inc_ref(v___y_5361_);
                            v___x_5425_ = lean_whnf(
                                v_snd_5416_,
                                v___y_5361_,
                                v___y_5362_,
                                v___y_5363_,
                                v___y_5364_,
                            );
                            if lean_obj_tag(v___x_5425_) == 0 {
                                v_a_5426_ = lean_ctor_get(v___x_5425_, 0);
                                v_isSharedCheck_5478_ = (!lean_is_exclusive(v___x_5425_)) as u8;
                                if v_isSharedCheck_5478_ == 0 {
                                    v___x_5428_ = v___x_5425_;
                                    v_isShared_5429_ = v_isSharedCheck_5478_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_5426_);
                                    lean_dec(v___x_5425_);
                                    v___x_5428_ = lean_box(0);
                                    v_isShared_5429_ = v_isSharedCheck_5478_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5424_);
                                lean_del_object(v___x_5418_);
                                lean_dec(v___x_5409_);
                                lean_del_object(v___x_5384_);
                                lean_dec(v_val_5382_);
                                lean_del_object(v___x_5370_);
                                lean_dec(v_snd_5368_);
                                lean_dec(v_mvarId_5356_);
                                v_a_5479_ = lean_ctor_get(v___x_5425_, 0);
                                v_isSharedCheck_5486_ = (!lean_is_exclusive(v___x_5425_)) as u8;
                                if v_isSharedCheck_5486_ == 0 {
                                    v___x_5481_ = v___x_5425_;
                                    v_isShared_5482_ = v_isSharedCheck_5486_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_5479_);
                                    lean_dec(v___x_5425_);
                                    v___x_5481_ = lean_box(0);
                                    v_isShared_5482_ = v_isSharedCheck_5486_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_5418_);
                            lean_dec(v_snd_5416_);
                            lean_dec(v___x_5409_);
                            lean_del_object(v___x_5384_);
                            lean_dec(v_val_5382_);
                            lean_del_object(v___x_5370_);
                            lean_dec(v_snd_5368_);
                            lean_dec(v_mvarId_5356_);
                            v_a_5487_ = lean_ctor_get(v___x_5423_, 0);
                            v_isSharedCheck_5494_ = (!lean_is_exclusive(v___x_5423_)) as u8;
                            if v_isSharedCheck_5494_ == 0 {
                                v___x_5489_ = v___x_5423_;
                                v_isShared_5490_ = v_isSharedCheck_5494_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_5487_);
                                lean_dec(v___x_5423_);
                                v___x_5489_ = lean_box(0);
                                v_isShared_5490_ = v_isSharedCheck_5494_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_5418_);
                        lean_dec(v_snd_5416_);
                        lean_dec(v_fst_5415_);
                        lean_dec(v___x_5409_);
                        lean_del_object(v___x_5384_);
                        lean_dec(v_val_5382_);
                        lean_dec(v_snd_5368_);
                        v_a_5374_ = v___x_5396_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5418_);
                    lean_dec(v_snd_5416_);
                    lean_dec(v_fst_5415_);
                    lean_dec(v___x_5409_);
                    lean_del_object(v___x_5384_);
                    lean_dec(v_val_5382_);
                    lean_del_object(v___x_5370_);
                    lean_dec(v_snd_5368_);
                    lean_dec(v_mvarId_5356_);
                    v_a_5495_ = lean_ctor_get(v___x_5420_, 0);
                    v_isSharedCheck_5502_ = (!lean_is_exclusive(v___x_5420_)) as u8;
                    if v_isSharedCheck_5502_ == 0 {
                        v___x_5497_ = v___x_5420_;
                        v_isShared_5498_ = v_isSharedCheck_5502_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_5495_);
                        lean_dec(v___x_5420_);
                        v___x_5497_ = lean_box(0);
                        v_isShared_5498_ = v_isSharedCheck_5502_;
                        state = 23;
                        continue;
                    }
                }
            }
            11 => {
                v___x_5476_ = l_Lean_Expr_isRawNatLit(v_a_5424_);
                lean_dec(v_a_5424_);
                if v___x_5476_ == 0 {
                    lean_dec(v_a_5426_);
                    v___y_5466_ = v___x_5476_;
                    state = 18;
                    continue;
                } else {
                    v___x_5477_ = l_Lean_Expr_isRawNatLit(v_a_5426_);
                    lean_dec(v_a_5426_);
                    v___y_5466_ = v___x_5477_;
                    state = 18;
                    continue;
                }
            }
            12 => {
                v___x_5431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0(v___x_5386_, v___x_5386_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
                v___y_5398_ = v___x_5431_;
                state = 7;
                continue;
            }
            13 => {
                if v___y_5434_ == 0 {
                    lean_del_object(v___x_5428_);
                    v_options_5435_ = lean_ctor_get(v___y_5363_, 2);
                    v_hasTrace_5436_ = lean_ctor_get_uint8(
                        v_options_5435_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5436_ == 0 {
                        lean_dec_ref(v___y_5433_);
                        lean_del_object(v___x_5418_);
                        lean_dec(v_val_5382_);
                        state = 12;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5437_ = lean_ctor_get(v___y_5363_, 13);
                        v___x_5438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4;
                        v___x_5439_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7);
                        v___x_5440_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5437_,
                            v_options_5435_,
                            v___x_5439_,
                        );
                        if v___x_5440_ == 0 {
                            lean_dec_ref(v___y_5433_);
                            lean_del_object(v___x_5418_);
                            lean_dec(v_val_5382_);
                            state = 12;
                            continue;
                        } else {
                            v___x_5441_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9);
                            v___x_5442_ = l_Lean_LocalDecl_userName(v_val_5382_);
                            lean_dec(v_val_5382_);
                            v___x_5443_ = l_Lean_MessageData_ofName(v___x_5442_);
                            if v_isShared_5419_ == 0 {
                                lean_ctor_set_tag(v___x_5418_, 7);
                                lean_ctor_set(v___x_5418_, 1, v___x_5443_);
                                lean_ctor_set(v___x_5418_, 0, v___x_5441_);
                                v___x_5445_ = v___x_5418_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_5461_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5461_, 0, v___x_5441_);
                                lean_ctor_set(v_reuseFailAlloc_5461_, 1, v___x_5443_);
                                v___x_5445_ = v_reuseFailAlloc_5461_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5418_);
                    lean_del_object(v___x_5384_);
                    lean_dec(v_val_5382_);
                    lean_del_object(v___x_5370_);
                    lean_dec(v_snd_5368_);
                    lean_dec(v_mvarId_5356_);
                    if v_isShared_5429_ == 0 {
                        lean_ctor_set_tag(v___x_5428_, 1);
                        lean_ctor_set(v___x_5428_, 0, v___y_5433_);
                        v___x_5463_ = v___x_5428_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_5464_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5464_, 0, v___y_5433_);
                        v___x_5463_ = v_reuseFailAlloc_5464_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                v___x_5446_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11);
                v___x_5447_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5447_, 0, v___x_5445_);
                lean_ctor_set(v___x_5447_, 1, v___x_5446_);
                v___x_5448_ = l_Lean_Exception_toMessageData(v___y_5433_);
                v___x_5449_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5449_, 0, v___x_5447_);
                lean_ctor_set(v___x_5449_, 1, v___x_5448_);
                v___x_5450_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1(v___x_5438_, v___x_5449_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
                if lean_obj_tag(v___x_5450_) == 0 {
                    v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
                    lean_inc(v_a_5451_);
                    lean_dec_ref_known(v___x_5450_, 1);
                    v___x_5452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0(v___x_5386_, v_a_5451_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
                    v___y_5398_ = v___x_5452_;
                    state = 7;
                    continue;
                } else {
                    lean_del_object(v___x_5384_);
                    lean_del_object(v___x_5370_);
                    lean_dec(v_snd_5368_);
                    lean_dec(v_mvarId_5356_);
                    v_a_5453_ = lean_ctor_get(v___x_5450_, 0);
                    v_isSharedCheck_5460_ = (!lean_is_exclusive(v___x_5450_)) as u8;
                    if v_isSharedCheck_5460_ == 0 {
                        v___x_5455_ = v___x_5450_;
                        v_isShared_5456_ = v_isSharedCheck_5460_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_5453_);
                        lean_dec(v___x_5450_);
                        v___x_5455_ = lean_box(0);
                        v_isShared_5456_ = v_isSharedCheck_5460_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_5456_ == 0 {
                    v___x_5458_ = v___x_5455_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5459_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_a_5453_);
                    v___x_5458_ = v_reuseFailAlloc_5459_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5458_;
            }
            17 => {
                return v___x_5463_;
            }
            18 => {
                if v___y_5466_ == 0 {
                    v___x_5467_ = lean_box(0);
                    lean_inc(v___x_5409_);
                    lean_inc(v_mvarId_5356_);
                    v___x_5468_ = l_Lean_Meta_injection(
                        v_mvarId_5356_,
                        v___x_5409_,
                        v___x_5467_,
                        v___y_5361_,
                        v___y_5362_,
                        v___y_5363_,
                        v___y_5364_,
                    );
                    if lean_obj_tag(v___x_5468_) == 0 {
                        lean_del_object(v___x_5428_);
                        lean_del_object(v___x_5418_);
                        lean_dec(v_val_5382_);
                        lean_del_object(v___x_5370_);
                        lean_dec(v_mvarId_5356_);
                        v_a_5469_ = lean_ctor_get(v___x_5468_, 0);
                        lean_inc(v_a_5469_);
                        lean_dec_ref_known(v___x_5468_, 1);
                        if lean_obj_tag(v_a_5469_) == 0 {
                            lean_dec(v___x_5409_);
                            v___x_5470_ = lean_box(0);
                            v_a_5388_ = v___x_5470_;
                            state = 5;
                            continue;
                        } else {
                            v_mvarId_5471_ = lean_ctor_get(v_a_5469_, 0);
                            lean_inc(v_mvarId_5471_);
                            lean_dec_ref_known(v_a_5469_, 3);
                            v___x_5472_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_5472_, 0, v___x_5409_);
                            lean_ctor_set(v___x_5472_, 1, v_mvarId_5471_);
                            v_a_5388_ = v___x_5472_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5409_);
                        v_a_5473_ = lean_ctor_get(v___x_5468_, 0);
                        lean_inc(v_a_5473_);
                        lean_dec_ref_known(v___x_5468_, 1);
                        v___x_5474_ = l_Lean_Exception_isInterrupt(v_a_5473_);
                        if v___x_5474_ == 0 {
                            lean_inc(v_a_5473_);
                            v___x_5475_ = l_Lean_Exception_isRuntime(v_a_5473_);
                            v___y_5433_ = v_a_5473_;
                            v___y_5434_ = v___x_5475_;
                            state = 13;
                            continue;
                        } else {
                            v___y_5433_ = v_a_5473_;
                            v___y_5434_ = v___x_5474_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5428_);
                    lean_del_object(v___x_5418_);
                    lean_dec(v___x_5409_);
                    lean_del_object(v___x_5384_);
                    lean_dec(v_val_5382_);
                    lean_dec(v_snd_5368_);
                    v_a_5374_ = v___x_5396_;
                    state = 2;
                    continue;
                }
            }
            19 => {
                if v_isShared_5482_ == 0 {
                    v___x_5484_ = v___x_5481_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5485_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5485_, 0, v_a_5479_);
                    v___x_5484_ = v_reuseFailAlloc_5485_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5484_;
            }
            21 => {
                if v_isShared_5490_ == 0 {
                    v___x_5492_ = v___x_5489_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5493_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_a_5487_);
                    v___x_5492_ = v_reuseFailAlloc_5493_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5492_;
            }
            23 => {
                if v_isShared_5498_ == 0 {
                    v___x_5500_ = v___x_5497_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5495_);
                    v___x_5500_ = v_reuseFailAlloc_5501_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5500_;
            }
            25 => {
                if v_isShared_5507_ == 0 {
                    v___x_5509_ = v___x_5506_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5504_);
                    v___x_5509_ = v_reuseFailAlloc_5510_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4_spec__7___boxed(
    mut v_forbidden_5515_: *mut LeanObject,
    mut v_mvarId_5516_: *mut LeanObject,
    mut v_as_5517_: *mut LeanObject,
    mut v_sz_5518_: *mut LeanObject,
    mut v_i_5519_: *mut LeanObject,
    mut v_b_5520_: *mut LeanObject,
    mut v___y_5521_: *mut LeanObject,
    mut v___y_5522_: *mut LeanObject,
    mut v___y_5523_: *mut LeanObject,
    mut v___y_5524_: *mut LeanObject,
    mut v___y_5525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5526_: usize = 0;
    let mut v_i_boxed_5527_: usize = 0;
    let mut v_res_5528_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5526_ = lean_unbox_usize(v_sz_5518_);
    lean_dec(v_sz_5518_);
    v_i_boxed_5527_ = lean_unbox_usize(v_i_5519_);
    lean_dec(v_i_5519_);
    v_res_5528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4_spec__7(v_forbidden_5515_, v_mvarId_5516_, v_as_5517_, v_sz_boxed_5526_, v_i_boxed_5527_, v_b_5520_, v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_);
    lean_dec(v___y_5524_);
    lean_dec_ref(v___y_5523_);
    lean_dec(v___y_5522_);
    lean_dec_ref(v___y_5521_);
    lean_dec_ref(v_as_5517_);
    lean_dec(v_forbidden_5515_);
    return v_res_5528_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4(
    mut v_forbidden_5529_: *mut LeanObject,
    mut v_mvarId_5530_: *mut LeanObject,
    mut v_as_5531_: *mut LeanObject,
    mut v_sz_5532_: usize,
    mut v_i_5533_: usize,
    mut v_b_5534_: *mut LeanObject,
    mut v___y_5535_: *mut LeanObject,
    mut v___y_5536_: *mut LeanObject,
    mut v___y_5537_: *mut LeanObject,
    mut v___y_5538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5540_: u8 = 0;
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5545_: u8 = 0;
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: usize = 0;
    let mut v___x_5552_: usize = 0;
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5559_: u8 = 0;
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5578_: u8 = 0;
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5582_: u8 = 0;
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: u8 = 0;
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5593_: u8 = 0;
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5603_: u8 = 0;
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5608_: u8 = 0;
    let mut v_options_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5610_: u8 = 0;
    let mut v_inheritedTraceOptions_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: u8 = 0;
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5630_: u8 = 0;
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5634_: u8 = 0;
    let mut v_reuseFailAlloc_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5640_: u8 = 0;
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: u8 = 0;
    let mut v___x_5649_: u8 = 0;
    let mut v___x_5650_: u8 = 0;
    let mut v___x_5651_: u8 = 0;
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_a_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5656_: u8 = 0;
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5660_: u8 = 0;
    let mut v_a_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5664_: u8 = 0;
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5668_: u8 = 0;
    let mut v_a_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5672_: u8 = 0;
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5676_: u8 = 0;
    let mut v_isSharedCheck_5677_: u8 = 0;
    let mut v_a_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5681_: u8 = 0;
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5685_: u8 = 0;
    let mut v_isSharedCheck_5686_: u8 = 0;
    let mut v_isSharedCheck_5687_: u8 = 0;
    let mut v_unused_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5540_ = lean_usize_dec_lt(v_i_5533_, v_sz_5532_);
                if v___x_5540_ == 0 {
                    lean_dec(v_mvarId_5530_);
                    v___x_5541_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5541_, 0, v_b_5534_);
                    return v___x_5541_;
                } else {
                    v_snd_5542_ = lean_ctor_get(v_b_5534_, 1);
                    v_isSharedCheck_5687_ = (!lean_is_exclusive(v_b_5534_)) as u8;
                    if v_isSharedCheck_5687_ == 0 {
                        v_unused_5688_ = lean_ctor_get(v_b_5534_, 0);
                        lean_dec(v_unused_5688_);
                        v___x_5544_ = v_b_5534_;
                        v_isShared_5545_ = v_isSharedCheck_5687_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5542_);
                        lean_dec(v_b_5534_);
                        v___x_5544_ = lean_box(0);
                        v_isShared_5545_ = v_isSharedCheck_5687_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5546_ = lean_box(0);
                v_a_5555_ = lean_array_uget(v_as_5531_, v_i_5533_);
                if lean_obj_tag(v_a_5555_) == 0 {
                    v_a_5548_ = v_snd_5542_;
                    state = 2;
                    continue;
                } else {
                    v_val_5556_ = lean_ctor_get(v_a_5555_, 0);
                    v_isSharedCheck_5686_ = (!lean_is_exclusive(v_a_5555_)) as u8;
                    if v_isSharedCheck_5686_ == 0 {
                        v___x_5558_ = v_a_5555_;
                        v_isShared_5559_ = v_isSharedCheck_5686_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_5556_);
                        lean_dec(v_a_5555_);
                        v___x_5558_ = lean_box(0);
                        v_isShared_5559_ = v_isSharedCheck_5686_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5545_ == 0 {
                    lean_ctor_set(v___x_5544_, 1, v_a_5548_);
                    lean_ctor_set(v___x_5544_, 0, v___x_5546_);
                    v___x_5550_ = v___x_5544_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5554_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5554_, 0, v___x_5546_);
                    lean_ctor_set(v_reuseFailAlloc_5554_, 1, v_a_5548_);
                    v___x_5550_ = v_reuseFailAlloc_5554_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5551_ = 1usize;
                v___x_5552_ = lean_usize_add(v_i_5533_, v___x_5551_);
                v___x_5553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4_spec__7(v_forbidden_5529_, v_mvarId_5530_, v_as_5531_, v_sz_5532_, v___x_5552_, v___x_5550_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
                return v___x_5553_;
            }
            4 => {
                v___x_5560_ = lean_box(0);
                v___x_5570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4_spec__7___closed__0;
                v___x_5583_ = l_Lean_LocalDecl_fvarId(v_val_5556_);
                v___x_5584_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0___redArg(v___x_5583_, v_forbidden_5529_);
                if v___x_5584_ == 0 {
                    v___x_5585_ = l_Lean_LocalDecl_type(v_val_5556_);
                    v___x_5586_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAnyCandidate_x3f(v___x_5585_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
                    if lean_obj_tag(v___x_5586_) == 0 {
                        v_a_5587_ = lean_ctor_get(v___x_5586_, 0);
                        lean_inc(v_a_5587_);
                        lean_dec_ref_known(v___x_5586_, 1);
                        if lean_obj_tag(v_a_5587_) == 1 {
                            v_val_5588_ = lean_ctor_get(v_a_5587_, 0);
                            lean_inc(v_val_5588_);
                            lean_dec_ref_known(v_a_5587_, 1);
                            v_fst_5589_ = lean_ctor_get(v_val_5588_, 0);
                            v_snd_5590_ = lean_ctor_get(v_val_5588_, 1);
                            v_isSharedCheck_5677_ = (!lean_is_exclusive(v_val_5588_)) as u8;
                            if v_isSharedCheck_5677_ == 0 {
                                v___x_5592_ = v_val_5588_;
                                v_isShared_5593_ = v_isSharedCheck_5677_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_snd_5590_);
                                lean_inc(v_fst_5589_);
                                lean_dec(v_val_5588_);
                                v___x_5592_ = lean_box(0);
                                v_isShared_5593_ = v_isSharedCheck_5677_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5587_);
                            lean_dec(v___x_5583_);
                            lean_del_object(v___x_5558_);
                            lean_dec(v_val_5556_);
                            lean_dec(v_snd_5542_);
                            v_a_5548_ = v___x_5570_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5583_);
                        lean_del_object(v___x_5558_);
                        lean_dec(v_val_5556_);
                        lean_del_object(v___x_5544_);
                        lean_dec(v_snd_5542_);
                        lean_dec(v_mvarId_5530_);
                        v_a_5678_ = lean_ctor_get(v___x_5586_, 0);
                        v_isSharedCheck_5685_ = (!lean_is_exclusive(v___x_5586_)) as u8;
                        if v_isSharedCheck_5685_ == 0 {
                            v___x_5680_ = v___x_5586_;
                            v_isShared_5681_ = v_isSharedCheck_5685_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_5678_);
                            lean_dec(v___x_5586_);
                            v___x_5680_ = lean_box(0);
                            v_isShared_5681_ = v_isSharedCheck_5685_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_5583_);
                    lean_del_object(v___x_5558_);
                    lean_dec(v_val_5556_);
                    lean_dec(v_snd_5542_);
                    v_a_5548_ = v___x_5570_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_5559_ == 0 {
                    lean_ctor_set(v___x_5558_, 0, v_a_5562_);
                    v___x_5564_ = v___x_5558_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_a_5562_);
                    v___x_5564_ = v_reuseFailAlloc_5569_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5565_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5565_, 0, v___x_5564_);
                lean_ctor_set(v___x_5565_, 1, v___x_5560_);
                v___x_5566_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5566_, 0, v___x_5565_);
                v___x_5567_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5567_, 0, v___x_5566_);
                lean_ctor_set(v___x_5567_, 1, v_snd_5542_);
                v___x_5568_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5568_, 0, v___x_5567_);
                return v___x_5568_;
            }
            7 => {
                if lean_obj_tag(v___y_5572_) == 0 {
                    v_a_5573_ = lean_ctor_get(v___y_5572_, 0);
                    lean_inc(v_a_5573_);
                    lean_dec_ref_known(v___y_5572_, 1);
                    if lean_obj_tag(v_a_5573_) == 0 {
                        lean_del_object(v___x_5544_);
                        lean_dec(v_mvarId_5530_);
                        v_a_5574_ = lean_ctor_get(v_a_5573_, 0);
                        lean_inc(v_a_5574_);
                        lean_dec_ref_known(v_a_5573_, 1);
                        v_a_5562_ = v_a_5574_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec_ref_known(v_a_5573_, 1);
                        lean_del_object(v___x_5558_);
                        lean_dec(v_snd_5542_);
                        v_a_5548_ = v___x_5570_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5558_);
                    lean_del_object(v___x_5544_);
                    lean_dec(v_snd_5542_);
                    lean_dec(v_mvarId_5530_);
                    v_a_5575_ = lean_ctor_get(v___y_5572_, 0);
                    v_isSharedCheck_5582_ = (!lean_is_exclusive(v___y_5572_)) as u8;
                    if v_isSharedCheck_5582_ == 0 {
                        v___x_5577_ = v___y_5572_;
                        v_isShared_5578_ = v_isSharedCheck_5582_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5575_);
                        lean_dec(v___y_5572_);
                        v___x_5577_ = lean_box(0);
                        v_isShared_5578_ = v_isSharedCheck_5582_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5578_ == 0 {
                    v___x_5580_ = v___x_5577_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
                    v___x_5580_ = v_reuseFailAlloc_5581_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5580_;
            }
            10 => {
                lean_inc(v_snd_5590_);
                lean_inc(v_fst_5589_);
                v___x_5594_ = l_Lean_Meta_isExprDefEq(
                    v_fst_5589_,
                    v_snd_5590_,
                    v___y_5535_,
                    v___y_5536_,
                    v___y_5537_,
                    v___y_5538_,
                );
                if lean_obj_tag(v___x_5594_) == 0 {
                    v_a_5595_ = lean_ctor_get(v___x_5594_, 0);
                    lean_inc(v_a_5595_);
                    lean_dec_ref_known(v___x_5594_, 1);
                    v___x_5596_ = (lean_unbox(v_a_5595_) as u8);
                    lean_dec(v_a_5595_);
                    if v___x_5596_ == 0 {
                        lean_inc(v___y_5538_);
                        lean_inc_ref(v___y_5537_);
                        lean_inc(v___y_5536_);
                        lean_inc_ref(v___y_5535_);
                        v___x_5597_ = lean_whnf(
                            v_fst_5589_,
                            v___y_5535_,
                            v___y_5536_,
                            v___y_5537_,
                            v___y_5538_,
                        );
                        if lean_obj_tag(v___x_5597_) == 0 {
                            v_a_5598_ = lean_ctor_get(v___x_5597_, 0);
                            lean_inc(v_a_5598_);
                            lean_dec_ref_known(v___x_5597_, 1);
                            lean_inc(v___y_5538_);
                            lean_inc_ref(v___y_5537_);
                            lean_inc(v___y_5536_);
                            lean_inc_ref(v___y_5535_);
                            v___x_5599_ = lean_whnf(
                                v_snd_5590_,
                                v___y_5535_,
                                v___y_5536_,
                                v___y_5537_,
                                v___y_5538_,
                            );
                            if lean_obj_tag(v___x_5599_) == 0 {
                                v_a_5600_ = lean_ctor_get(v___x_5599_, 0);
                                v_isSharedCheck_5652_ = (!lean_is_exclusive(v___x_5599_)) as u8;
                                if v_isSharedCheck_5652_ == 0 {
                                    v___x_5602_ = v___x_5599_;
                                    v_isShared_5603_ = v_isSharedCheck_5652_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_5600_);
                                    lean_dec(v___x_5599_);
                                    v___x_5602_ = lean_box(0);
                                    v_isShared_5603_ = v_isSharedCheck_5652_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5598_);
                                lean_del_object(v___x_5592_);
                                lean_dec(v___x_5583_);
                                lean_del_object(v___x_5558_);
                                lean_dec(v_val_5556_);
                                lean_del_object(v___x_5544_);
                                lean_dec(v_snd_5542_);
                                lean_dec(v_mvarId_5530_);
                                v_a_5653_ = lean_ctor_get(v___x_5599_, 0);
                                v_isSharedCheck_5660_ = (!lean_is_exclusive(v___x_5599_)) as u8;
                                if v_isSharedCheck_5660_ == 0 {
                                    v___x_5655_ = v___x_5599_;
                                    v_isShared_5656_ = v_isSharedCheck_5660_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_5653_);
                                    lean_dec(v___x_5599_);
                                    v___x_5655_ = lean_box(0);
                                    v_isShared_5656_ = v_isSharedCheck_5660_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_5592_);
                            lean_dec(v_snd_5590_);
                            lean_dec(v___x_5583_);
                            lean_del_object(v___x_5558_);
                            lean_dec(v_val_5556_);
                            lean_del_object(v___x_5544_);
                            lean_dec(v_snd_5542_);
                            lean_dec(v_mvarId_5530_);
                            v_a_5661_ = lean_ctor_get(v___x_5597_, 0);
                            v_isSharedCheck_5668_ = (!lean_is_exclusive(v___x_5597_)) as u8;
                            if v_isSharedCheck_5668_ == 0 {
                                v___x_5663_ = v___x_5597_;
                                v_isShared_5664_ = v_isSharedCheck_5668_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_5661_);
                                lean_dec(v___x_5597_);
                                v___x_5663_ = lean_box(0);
                                v_isShared_5664_ = v_isSharedCheck_5668_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_5592_);
                        lean_dec(v_snd_5590_);
                        lean_dec(v_fst_5589_);
                        lean_dec(v___x_5583_);
                        lean_del_object(v___x_5558_);
                        lean_dec(v_val_5556_);
                        lean_dec(v_snd_5542_);
                        v_a_5548_ = v___x_5570_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5592_);
                    lean_dec(v_snd_5590_);
                    lean_dec(v_fst_5589_);
                    lean_dec(v___x_5583_);
                    lean_del_object(v___x_5558_);
                    lean_dec(v_val_5556_);
                    lean_del_object(v___x_5544_);
                    lean_dec(v_snd_5542_);
                    lean_dec(v_mvarId_5530_);
                    v_a_5669_ = lean_ctor_get(v___x_5594_, 0);
                    v_isSharedCheck_5676_ = (!lean_is_exclusive(v___x_5594_)) as u8;
                    if v_isSharedCheck_5676_ == 0 {
                        v___x_5671_ = v___x_5594_;
                        v_isShared_5672_ = v_isSharedCheck_5676_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_5669_);
                        lean_dec(v___x_5594_);
                        v___x_5671_ = lean_box(0);
                        v_isShared_5672_ = v_isSharedCheck_5676_;
                        state = 23;
                        continue;
                    }
                }
            }
            11 => {
                v___x_5650_ = l_Lean_Expr_isRawNatLit(v_a_5598_);
                lean_dec(v_a_5598_);
                if v___x_5650_ == 0 {
                    lean_dec(v_a_5600_);
                    v___y_5640_ = v___x_5650_;
                    state = 18;
                    continue;
                } else {
                    v___x_5651_ = l_Lean_Expr_isRawNatLit(v_a_5600_);
                    lean_dec(v_a_5600_);
                    v___y_5640_ = v___x_5651_;
                    state = 18;
                    continue;
                }
            }
            12 => {
                v___x_5605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0(v___x_5560_, v___x_5560_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
                v___y_5572_ = v___x_5605_;
                state = 7;
                continue;
            }
            13 => {
                if v___y_5608_ == 0 {
                    lean_del_object(v___x_5602_);
                    v_options_5609_ = lean_ctor_get(v___y_5537_, 2);
                    v_hasTrace_5610_ = lean_ctor_get_uint8(
                        v_options_5609_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5610_ == 0 {
                        lean_dec_ref(v___y_5607_);
                        lean_del_object(v___x_5592_);
                        lean_dec(v_val_5556_);
                        state = 12;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5611_ = lean_ctor_get(v___y_5537_, 13);
                        v___x_5612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4;
                        v___x_5613_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7);
                        v___x_5614_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5611_,
                            v_options_5609_,
                            v___x_5613_,
                        );
                        if v___x_5614_ == 0 {
                            lean_dec_ref(v___y_5607_);
                            lean_del_object(v___x_5592_);
                            lean_dec(v_val_5556_);
                            state = 12;
                            continue;
                        } else {
                            v___x_5615_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__9);
                            v___x_5616_ = l_Lean_LocalDecl_userName(v_val_5556_);
                            lean_dec(v_val_5556_);
                            v___x_5617_ = l_Lean_MessageData_ofName(v___x_5616_);
                            if v_isShared_5593_ == 0 {
                                lean_ctor_set_tag(v___x_5592_, 7);
                                lean_ctor_set(v___x_5592_, 1, v___x_5617_);
                                lean_ctor_set(v___x_5592_, 0, v___x_5615_);
                                v___x_5619_ = v___x_5592_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_5635_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5635_, 0, v___x_5615_);
                                lean_ctor_set(v_reuseFailAlloc_5635_, 1, v___x_5617_);
                                v___x_5619_ = v_reuseFailAlloc_5635_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5592_);
                    lean_del_object(v___x_5558_);
                    lean_dec(v_val_5556_);
                    lean_del_object(v___x_5544_);
                    lean_dec(v_snd_5542_);
                    lean_dec(v_mvarId_5530_);
                    if v_isShared_5603_ == 0 {
                        lean_ctor_set_tag(v___x_5602_, 1);
                        lean_ctor_set(v___x_5602_, 0, v___y_5607_);
                        v___x_5637_ = v___x_5602_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_5638_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5638_, 0, v___y_5607_);
                        v___x_5637_ = v_reuseFailAlloc_5638_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                v___x_5620_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__11);
                v___x_5621_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5621_, 0, v___x_5619_);
                lean_ctor_set(v___x_5621_, 1, v___x_5620_);
                v___x_5622_ = l_Lean_Exception_toMessageData(v___y_5607_);
                v___x_5623_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5623_, 0, v___x_5621_);
                lean_ctor_set(v___x_5623_, 1, v___x_5622_);
                v___x_5624_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1(v___x_5612_, v___x_5623_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
                if lean_obj_tag(v___x_5624_) == 0 {
                    v_a_5625_ = lean_ctor_get(v___x_5624_, 0);
                    lean_inc(v_a_5625_);
                    lean_dec_ref_known(v___x_5624_, 1);
                    v___x_5626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___lam__0(v___x_5560_, v_a_5625_, v___y_5535_, v___y_5536_, v___y_5537_, v___y_5538_);
                    v___y_5572_ = v___x_5626_;
                    state = 7;
                    continue;
                } else {
                    lean_del_object(v___x_5558_);
                    lean_del_object(v___x_5544_);
                    lean_dec(v_snd_5542_);
                    lean_dec(v_mvarId_5530_);
                    v_a_5627_ = lean_ctor_get(v___x_5624_, 0);
                    v_isSharedCheck_5634_ = (!lean_is_exclusive(v___x_5624_)) as u8;
                    if v_isSharedCheck_5634_ == 0 {
                        v___x_5629_ = v___x_5624_;
                        v_isShared_5630_ = v_isSharedCheck_5634_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_5627_);
                        lean_dec(v___x_5624_);
                        v___x_5629_ = lean_box(0);
                        v_isShared_5630_ = v_isSharedCheck_5634_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_5630_ == 0 {
                    v___x_5632_ = v___x_5629_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_a_5627_);
                    v___x_5632_ = v_reuseFailAlloc_5633_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5632_;
            }
            17 => {
                return v___x_5637_;
            }
            18 => {
                if v___y_5640_ == 0 {
                    v___x_5641_ = lean_box(0);
                    lean_inc(v___x_5583_);
                    lean_inc(v_mvarId_5530_);
                    v___x_5642_ = l_Lean_Meta_injection(
                        v_mvarId_5530_,
                        v___x_5583_,
                        v___x_5641_,
                        v___y_5535_,
                        v___y_5536_,
                        v___y_5537_,
                        v___y_5538_,
                    );
                    if lean_obj_tag(v___x_5642_) == 0 {
                        lean_del_object(v___x_5602_);
                        lean_del_object(v___x_5592_);
                        lean_dec(v_val_5556_);
                        lean_del_object(v___x_5544_);
                        lean_dec(v_mvarId_5530_);
                        v_a_5643_ = lean_ctor_get(v___x_5642_, 0);
                        lean_inc(v_a_5643_);
                        lean_dec_ref_known(v___x_5642_, 1);
                        if lean_obj_tag(v_a_5643_) == 0 {
                            lean_dec(v___x_5583_);
                            v___x_5644_ = lean_box(0);
                            v_a_5562_ = v___x_5644_;
                            state = 5;
                            continue;
                        } else {
                            v_mvarId_5645_ = lean_ctor_get(v_a_5643_, 0);
                            lean_inc(v_mvarId_5645_);
                            lean_dec_ref_known(v_a_5643_, 3);
                            v___x_5646_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_5646_, 0, v___x_5583_);
                            lean_ctor_set(v___x_5646_, 1, v_mvarId_5645_);
                            v_a_5562_ = v___x_5646_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5583_);
                        v_a_5647_ = lean_ctor_get(v___x_5642_, 0);
                        lean_inc(v_a_5647_);
                        lean_dec_ref_known(v___x_5642_, 1);
                        v___x_5648_ = l_Lean_Exception_isInterrupt(v_a_5647_);
                        if v___x_5648_ == 0 {
                            lean_inc(v_a_5647_);
                            v___x_5649_ = l_Lean_Exception_isRuntime(v_a_5647_);
                            v___y_5607_ = v_a_5647_;
                            v___y_5608_ = v___x_5649_;
                            state = 13;
                            continue;
                        } else {
                            v___y_5607_ = v_a_5647_;
                            v___y_5608_ = v___x_5648_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5602_);
                    lean_del_object(v___x_5592_);
                    lean_dec(v___x_5583_);
                    lean_del_object(v___x_5558_);
                    lean_dec(v_val_5556_);
                    lean_dec(v_snd_5542_);
                    v_a_5548_ = v___x_5570_;
                    state = 2;
                    continue;
                }
            }
            19 => {
                if v_isShared_5656_ == 0 {
                    v___x_5658_ = v___x_5655_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5659_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_a_5653_);
                    v___x_5658_ = v_reuseFailAlloc_5659_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5658_;
            }
            21 => {
                if v_isShared_5664_ == 0 {
                    v___x_5666_ = v___x_5663_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_a_5661_);
                    v___x_5666_ = v_reuseFailAlloc_5667_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5666_;
            }
            23 => {
                if v_isShared_5672_ == 0 {
                    v___x_5674_ = v___x_5671_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5675_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_a_5669_);
                    v___x_5674_ = v_reuseFailAlloc_5675_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5674_;
            }
            25 => {
                if v_isShared_5681_ == 0 {
                    v___x_5683_ = v___x_5680_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5684_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5684_, 0, v_a_5678_);
                    v___x_5683_ = v_reuseFailAlloc_5684_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4___boxed(
    mut v_forbidden_5689_: *mut LeanObject,
    mut v_mvarId_5690_: *mut LeanObject,
    mut v_as_5691_: *mut LeanObject,
    mut v_sz_5692_: *mut LeanObject,
    mut v_i_5693_: *mut LeanObject,
    mut v_b_5694_: *mut LeanObject,
    mut v___y_5695_: *mut LeanObject,
    mut v___y_5696_: *mut LeanObject,
    mut v___y_5697_: *mut LeanObject,
    mut v___y_5698_: *mut LeanObject,
    mut v___y_5699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5700_: usize = 0;
    let mut v_i_boxed_5701_: usize = 0;
    let mut v_res_5702_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5700_ = lean_unbox_usize(v_sz_5692_);
    lean_dec(v_sz_5692_);
    v_i_boxed_5701_ = lean_unbox_usize(v_i_5693_);
    lean_dec(v_i_5693_);
    v_res_5702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4(v_forbidden_5689_, v_mvarId_5690_, v_as_5691_, v_sz_boxed_5700_, v_i_boxed_5701_, v_b_5694_, v___y_5695_, v___y_5696_, v___y_5697_, v___y_5698_);
    lean_dec(v___y_5698_);
    lean_dec_ref(v___y_5697_);
    lean_dec(v___y_5696_);
    lean_dec_ref(v___y_5695_);
    lean_dec_ref(v_as_5691_);
    lean_dec(v_forbidden_5689_);
    return v_res_5702_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2(
    mut v_forbidden_5703_: *mut LeanObject,
    mut v_mvarId_5704_: *mut LeanObject,
    mut v_t_5705_: *mut LeanObject,
    mut v_init_5706_: *mut LeanObject,
    mut v___y_5707_: *mut LeanObject,
    mut v___y_5708_: *mut LeanObject,
    mut v___y_5709_: *mut LeanObject,
    mut v___y_5710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5718_: u8 = 0;
    let mut v_a_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5726_: usize = 0;
    let mut v___x_5727_: usize = 0;
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v_fst_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5742_: u8 = 0;
    let mut v_a_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5746_: u8 = 0;
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5750_: u8 = 0;
    let mut v_isSharedCheck_5751_: u8 = 0;
    let mut v_a_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5755_: u8 = 0;
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5712_ = lean_ctor_get(v_t_5705_, 0);
                v_tail_5713_ = lean_ctor_get(v_t_5705_, 1);
                lean_inc(v_mvarId_5704_);
                lean_inc_ref(v_init_5706_);
                v___x_5714_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3(v_init_5706_, v_forbidden_5703_, v_mvarId_5704_, v_root_5712_, v_init_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_);
                lean_dec_ref(v_init_5706_);
                if lean_obj_tag(v___x_5714_) == 0 {
                    v_a_5715_ = lean_ctor_get(v___x_5714_, 0);
                    v_isSharedCheck_5751_ = (!lean_is_exclusive(v___x_5714_)) as u8;
                    if v_isSharedCheck_5751_ == 0 {
                        v___x_5717_ = v___x_5714_;
                        v_isShared_5718_ = v_isSharedCheck_5751_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5715_);
                        lean_dec(v___x_5714_);
                        v___x_5717_ = lean_box(0);
                        v_isShared_5718_ = v_isSharedCheck_5751_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarId_5704_);
                    v_a_5752_ = lean_ctor_get(v___x_5714_, 0);
                    v_isSharedCheck_5759_ = (!lean_is_exclusive(v___x_5714_)) as u8;
                    if v_isSharedCheck_5759_ == 0 {
                        v___x_5754_ = v___x_5714_;
                        v_isShared_5755_ = v_isSharedCheck_5759_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5752_);
                        lean_dec(v___x_5714_);
                        v___x_5754_ = lean_box(0);
                        v_isShared_5755_ = v_isSharedCheck_5759_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_5715_) == 0 {
                    lean_dec(v_mvarId_5704_);
                    v_a_5719_ = lean_ctor_get(v_a_5715_, 0);
                    lean_inc(v_a_5719_);
                    lean_dec_ref_known(v_a_5715_, 1);
                    if v_isShared_5718_ == 0 {
                        lean_ctor_set(v___x_5717_, 0, v_a_5719_);
                        v___x_5721_ = v___x_5717_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5722_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5722_, 0, v_a_5719_);
                        v___x_5721_ = v_reuseFailAlloc_5722_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5717_);
                    v_a_5723_ = lean_ctor_get(v_a_5715_, 0);
                    lean_inc(v_a_5723_);
                    lean_dec_ref_known(v_a_5715_, 1);
                    v___x_5724_ = lean_box(0);
                    v___x_5725_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5725_, 0, v___x_5724_);
                    lean_ctor_set(v___x_5725_, 1, v_a_5723_);
                    v_sz_5726_ = lean_array_size(v_tail_5713_);
                    v___x_5727_ = 0usize;
                    v___x_5728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__4(v_forbidden_5703_, v_mvarId_5704_, v_tail_5713_, v_sz_5726_, v___x_5727_, v___x_5725_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_);
                    if lean_obj_tag(v___x_5728_) == 0 {
                        v_a_5729_ = lean_ctor_get(v___x_5728_, 0);
                        v_isSharedCheck_5742_ = (!lean_is_exclusive(v___x_5728_)) as u8;
                        if v_isSharedCheck_5742_ == 0 {
                            v___x_5731_ = v___x_5728_;
                            v_isShared_5732_ = v_isSharedCheck_5742_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5729_);
                            lean_dec(v___x_5728_);
                            v___x_5731_ = lean_box(0);
                            v_isShared_5732_ = v_isSharedCheck_5742_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5743_ = lean_ctor_get(v___x_5728_, 0);
                        v_isSharedCheck_5750_ = (!lean_is_exclusive(v___x_5728_)) as u8;
                        if v_isSharedCheck_5750_ == 0 {
                            v___x_5745_ = v___x_5728_;
                            v_isShared_5746_ = v_isSharedCheck_5750_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5743_);
                            lean_dec(v___x_5728_);
                            v___x_5745_ = lean_box(0);
                            v_isShared_5746_ = v_isSharedCheck_5750_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5721_;
            }
            3 => {
                v_fst_5733_ = lean_ctor_get(v_a_5729_, 0);
                if lean_obj_tag(v_fst_5733_) == 0 {
                    v_snd_5734_ = lean_ctor_get(v_a_5729_, 1);
                    lean_inc(v_snd_5734_);
                    lean_dec(v_a_5729_);
                    if v_isShared_5732_ == 0 {
                        lean_ctor_set(v___x_5731_, 0, v_snd_5734_);
                        v___x_5736_ = v___x_5731_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5737_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_snd_5734_);
                        v___x_5736_ = v_reuseFailAlloc_5737_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5733_);
                    lean_dec(v_a_5729_);
                    v_val_5738_ = lean_ctor_get(v_fst_5733_, 0);
                    lean_inc(v_val_5738_);
                    lean_dec_ref_known(v_fst_5733_, 1);
                    if v_isShared_5732_ == 0 {
                        lean_ctor_set(v___x_5731_, 0, v_val_5738_);
                        v___x_5740_ = v___x_5731_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5741_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5741_, 0, v_val_5738_);
                        v___x_5740_ = v_reuseFailAlloc_5741_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5736_;
            }
            5 => {
                return v___x_5740_;
            }
            6 => {
                if v_isShared_5746_ == 0 {
                    v___x_5748_ = v___x_5745_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5749_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5749_, 0, v_a_5743_);
                    v___x_5748_ = v_reuseFailAlloc_5749_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5748_;
            }
            8 => {
                if v_isShared_5755_ == 0 {
                    v___x_5757_ = v___x_5754_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5758_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_a_5752_);
                    v___x_5757_ = v_reuseFailAlloc_5758_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2___boxed(
    mut v_forbidden_5760_: *mut LeanObject,
    mut v_mvarId_5761_: *mut LeanObject,
    mut v_t_5762_: *mut LeanObject,
    mut v_init_5763_: *mut LeanObject,
    mut v___y_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5769_: *mut LeanObject = core::ptr::null_mut();
    v_res_5769_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2(v_forbidden_5760_, v_mvarId_5761_, v_t_5762_, v_init_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
    lean_dec(v___y_5767_);
    lean_dec_ref(v___y_5766_);
    lean_dec(v___y_5765_);
    lean_dec_ref(v___y_5764_);
    lean_dec_ref(v_t_5762_);
    lean_dec(v_forbidden_5760_);
    return v_res_5769_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny___lam__0(
    mut v_forbidden_5773_: *mut LeanObject,
    mut v_mvarId_5774_: *mut LeanObject,
    mut v___y_5775_: *mut LeanObject,
    mut v___y_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v_fst_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5797_: u8 = 0;
    let mut v_a_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5801_: u8 = 0;
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_5780_ = lean_ctor_get(v___y_5775_, 2);
                v_decls_5781_ = lean_ctor_get(v_lctx_5780_, 1);
                v___x_5782_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny___lam__0___closed__0;
                v___x_5783_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2(v_forbidden_5773_, v_mvarId_5774_, v_decls_5781_, v___x_5782_, v___y_5775_, v___y_5776_, v___y_5777_, v___y_5778_);
                if lean_obj_tag(v___x_5783_) == 0 {
                    v_a_5784_ = lean_ctor_get(v___x_5783_, 0);
                    v_isSharedCheck_5797_ = (!lean_is_exclusive(v___x_5783_)) as u8;
                    if v_isSharedCheck_5797_ == 0 {
                        v___x_5786_ = v___x_5783_;
                        v_isShared_5787_ = v_isSharedCheck_5797_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5784_);
                        lean_dec(v___x_5783_);
                        v___x_5786_ = lean_box(0);
                        v_isShared_5787_ = v_isSharedCheck_5797_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5798_ = lean_ctor_get(v___x_5783_, 0);
                    v_isSharedCheck_5805_ = (!lean_is_exclusive(v___x_5783_)) as u8;
                    if v_isSharedCheck_5805_ == 0 {
                        v___x_5800_ = v___x_5783_;
                        v_isShared_5801_ = v_isSharedCheck_5805_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5798_);
                        lean_dec(v___x_5783_);
                        v___x_5800_ = lean_box(0);
                        v_isShared_5801_ = v_isSharedCheck_5805_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5788_ = lean_ctor_get(v_a_5784_, 0);
                lean_inc(v_fst_5788_);
                lean_dec(v_a_5784_);
                if lean_obj_tag(v_fst_5788_) == 0 {
                    v___x_5789_ = lean_box(1);
                    if v_isShared_5787_ == 0 {
                        lean_ctor_set(v___x_5786_, 0, v___x_5789_);
                        v___x_5791_ = v___x_5786_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5792_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5792_, 0, v___x_5789_);
                        v___x_5791_ = v_reuseFailAlloc_5792_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5793_ = lean_ctor_get(v_fst_5788_, 0);
                    lean_inc(v_val_5793_);
                    lean_dec_ref_known(v_fst_5788_, 1);
                    if v_isShared_5787_ == 0 {
                        lean_ctor_set(v___x_5786_, 0, v_val_5793_);
                        v___x_5795_ = v___x_5786_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5796_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5796_, 0, v_val_5793_);
                        v___x_5795_ = v_reuseFailAlloc_5796_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5791_;
            }
            3 => {
                return v___x_5795_;
            }
            4 => {
                if v_isShared_5801_ == 0 {
                    v___x_5803_ = v___x_5800_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5804_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5804_, 0, v_a_5798_);
                    v___x_5803_ = v_reuseFailAlloc_5804_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny___lam__0___boxed(
    mut v_forbidden_5806_: *mut LeanObject,
    mut v_mvarId_5807_: *mut LeanObject,
    mut v___y_5808_: *mut LeanObject,
    mut v___y_5809_: *mut LeanObject,
    mut v___y_5810_: *mut LeanObject,
    mut v___y_5811_: *mut LeanObject,
    mut v___y_5812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5813_: *mut LeanObject = core::ptr::null_mut();
    v_res_5813_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny___lam__0(
        v_forbidden_5806_,
        v_mvarId_5807_,
        v___y_5808_,
        v___y_5809_,
        v___y_5810_,
        v___y_5811_,
    );
    lean_dec(v___y_5811_);
    lean_dec_ref(v___y_5810_);
    lean_dec(v___y_5809_);
    lean_dec_ref(v___y_5808_);
    lean_dec(v_forbidden_5806_);
    return v_res_5813_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny(
    mut v_mvarId_5814_: *mut LeanObject,
    mut v_forbidden_5815_: *mut LeanObject,
    mut v_a_5816_: *mut LeanObject,
    mut v_a_5817_: *mut LeanObject,
    mut v_a_5818_: *mut LeanObject,
    mut v_a_5819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_5814_);
    v___f_5821_ = lean_alloc_closure(
        l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_5821_, 0, v_forbidden_5815_);
    lean_closure_set(v___f_5821_, 1, v_mvarId_5814_);
    v___x_5822_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick_spec__4___redArg(v_mvarId_5814_, v___f_5821_, v_a_5816_, v_a_5817_, v_a_5818_, v_a_5819_);
    return v___x_5822_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny___boxed(
    mut v_mvarId_5823_: *mut LeanObject,
    mut v_forbidden_5824_: *mut LeanObject,
    mut v_a_5825_: *mut LeanObject,
    mut v_a_5826_: *mut LeanObject,
    mut v_a_5827_: *mut LeanObject,
    mut v_a_5828_: *mut LeanObject,
    mut v_a_5829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5830_: *mut LeanObject = core::ptr::null_mut();
    v_res_5830_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny(
        v_mvarId_5823_,
        v_forbidden_5824_,
        v_a_5825_,
        v_a_5826_,
        v_a_5827_,
        v_a_5828_,
    );
    lean_dec(v_a_5828_);
    lean_dec_ref(v_a_5827_);
    lean_dec(v_a_5826_);
    lean_dec_ref(v_a_5825_);
    return v_res_5830_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0(
    mut v_00_u03b2_5831_: *mut LeanObject,
    mut v_k_5832_: *mut LeanObject,
    mut v_t_5833_: *mut LeanObject,
) -> u8 {
    let mut v___x_5834_: u8 = 0;
    v___x_5834_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0___redArg(v_k_5832_, v_t_5833_);
    return v___x_5834_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0___boxed(
    mut v_00_u03b2_5835_: *mut LeanObject,
    mut v_k_5836_: *mut LeanObject,
    mut v_t_5837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5838_: u8 = 0;
    let mut v_r_5839_: *mut LeanObject = core::ptr::null_mut();
    v_res_5838_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__0(v_00_u03b2_5835_, v_k_5836_, v_t_5837_);
    lean_dec(v_t_5837_);
    lean_dec(v_k_5836_);
    v_r_5839_ = lean_box((v_res_5838_) as usize);
    return v_r_5839_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop_spec__0___redArg(
    mut v_msg_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5851_: u8 = 0;
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5856_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5846_ = lean_ctor_get(v___y_5843_, 5);
                v___x_5847_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1_spec__1(v_msg_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
                v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
                v_isSharedCheck_5856_ = (!lean_is_exclusive(v___x_5847_)) as u8;
                if v_isSharedCheck_5856_ == 0 {
                    v___x_5850_ = v___x_5847_;
                    v_isShared_5851_ = v_isSharedCheck_5856_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5848_);
                    lean_dec(v___x_5847_);
                    v___x_5850_ = lean_box(0);
                    v_isShared_5851_ = v_isSharedCheck_5856_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_5846_);
                v___x_5852_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5852_, 0, v_ref_5846_);
                lean_ctor_set(v___x_5852_, 1, v_a_5848_);
                if v_isShared_5851_ == 0 {
                    lean_ctor_set_tag(v___x_5850_, 1);
                    lean_ctor_set(v___x_5850_, 0, v___x_5852_);
                    v___x_5854_ = v___x_5850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5855_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5855_, 0, v___x_5852_);
                    v___x_5854_ = v_reuseFailAlloc_5855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5854_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop_spec__0___redArg___boxed(
    mut v_msg_5857_: *mut LeanObject,
    mut v___y_5858_: *mut LeanObject,
    mut v___y_5859_: *mut LeanObject,
    mut v___y_5860_: *mut LeanObject,
    mut v___y_5861_: *mut LeanObject,
    mut v___y_5862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5863_: *mut LeanObject = core::ptr::null_mut();
    v_res_5863_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop_spec__0___redArg(v_msg_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_);
    lean_dec(v___y_5861_);
    lean_dec_ref(v___y_5860_);
    lean_dec(v___y_5859_);
    lean_dec_ref(v___y_5858_);
    return v_res_5863_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__1()
-> *mut LeanObject {
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    v___x_5865_ =
        l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__0;
    v___x_5866_ = l_Lean_stringToMessageData(v___x_5865_);
    return v___x_5866_;
}
pub unsafe fn _init_l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__3()
-> *mut LeanObject {
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    v___x_5868_ =
        l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__2;
    v___x_5869_ = l_Lean_stringToMessageData(v___x_5868_);
    return v___x_5869_;
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop(
    mut v_mvarId_5870_: *mut LeanObject,
    mut v_forbidden_5871_: *mut LeanObject,
    mut v_a_5872_: *mut LeanObject,
    mut v_a_5873_: *mut LeanObject,
    mut v_a_5874_: *mut LeanObject,
    mut v_a_5875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5886_: u8 = 0;
    let mut v___x_5887_: u8 = 0;
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5892_: u8 = 0;
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: u8 = 0;
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: u8 = 0;
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5908_: u8 = 0;
    let mut v___x_5909_: u8 = 0;
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5919_: u8 = 0;
    let mut v_a_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5923_: u8 = 0;
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5927_: u8 = 0;
    let mut v_a_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5931_: u8 = 0;
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5935_: u8 = 0;
    let mut v_fvarId_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5940_: u8 = 0;
    let mut v_a_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5944_: u8 = 0;
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5948_: u8 = 0;
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5953_: u8 = 0;
    let mut v_a_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5957_: u8 = 0;
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5961_: u8 = 0;
    let mut v_options_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5963_: u8 = 0;
    let mut v_inheritedTraceOptions_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: u8 = 0;
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5962_ = lean_ctor_get(v_a_5874_, 2);
                v_hasTrace_5963_ = lean_ctor_get_uint8(
                    v_options_5962_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_hasTrace_5963_ == 0 {
                    v___y_5878_ = v_a_5872_;
                    v___y_5879_ = v_a_5873_;
                    v___y_5880_ = v_a_5874_;
                    v___y_5881_ = v_a_5875_;
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_5964_ = lean_ctor_get(v_a_5874_, 13);
                    v_cls_5965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4;
                    v___x_5966_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7);
                    v___x_5967_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_5964_,
                        v_options_5962_,
                        v___x_5966_,
                    );
                    if v___x_5967_ == 0 {
                        v___y_5878_ = v_a_5872_;
                        v___y_5879_ = v_a_5873_;
                        v___y_5880_ = v_a_5874_;
                        v___y_5881_ = v_a_5875_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5968_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__3_once), _init_l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__3);
                        lean_inc(v_mvarId_5870_);
                        v___x_5969_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_5969_, 0, v_mvarId_5870_);
                        v___x_5970_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5970_, 0, v___x_5968_);
                        lean_ctor_set(v___x_5970_, 1, v___x_5969_);
                        v___x_5971_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1(v_cls_5965_, v___x_5970_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_);
                        if lean_obj_tag(v___x_5971_) == 0 {
                            lean_dec_ref_known(v___x_5971_, 1);
                            v___y_5878_ = v_a_5872_;
                            v___y_5879_ = v_a_5873_;
                            v___y_5880_ = v_a_5874_;
                            v___y_5881_ = v_a_5875_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_forbidden_5871_);
                            lean_dec(v_mvarId_5870_);
                            return v___x_5971_;
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_mvarId_5870_);
                v___x_5882_ =
                    l___private_Lean_Meta_Match_SolveOverlap_0__Lean_MVarId_contradictionQuick(
                        v_mvarId_5870_,
                        v___y_5878_,
                        v___y_5879_,
                        v___y_5880_,
                        v___y_5881_,
                    );
                if lean_obj_tag(v___x_5882_) == 0 {
                    v_a_5883_ = lean_ctor_get(v___x_5882_, 0);
                    v_isSharedCheck_5953_ = (!lean_is_exclusive(v___x_5882_)) as u8;
                    if v_isSharedCheck_5953_ == 0 {
                        v___x_5885_ = v___x_5882_;
                        v_isShared_5886_ = v_isSharedCheck_5953_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5883_);
                        lean_dec(v___x_5882_);
                        v___x_5885_ = lean_box(0);
                        v_isShared_5886_ = v_isSharedCheck_5953_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_forbidden_5871_);
                    lean_dec(v_mvarId_5870_);
                    v_a_5954_ = lean_ctor_get(v___x_5882_, 0);
                    v_isSharedCheck_5961_ = (!lean_is_exclusive(v___x_5882_)) as u8;
                    if v_isSharedCheck_5961_ == 0 {
                        v___x_5956_ = v___x_5882_;
                        v_isShared_5957_ = v_isSharedCheck_5961_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_5954_);
                        lean_dec(v___x_5882_);
                        v___x_5956_ = lean_box(0);
                        v_isShared_5957_ = v_isSharedCheck_5961_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5887_ = (lean_unbox(v_a_5883_) as u8);
                if v___x_5887_ == 0 {
                    lean_del_object(v___x_5885_);
                    lean_inc(v_forbidden_5871_);
                    lean_inc(v_mvarId_5870_);
                    v___x_5888_ =
                        l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny(
                            v_mvarId_5870_,
                            v_forbidden_5871_,
                            v___y_5878_,
                            v___y_5879_,
                            v___y_5880_,
                            v___y_5881_,
                        );
                    if lean_obj_tag(v___x_5888_) == 0 {
                        v_a_5889_ = lean_ctor_get(v___x_5888_, 0);
                        v_isSharedCheck_5940_ = (!lean_is_exclusive(v___x_5888_)) as u8;
                        if v_isSharedCheck_5940_ == 0 {
                            v___x_5891_ = v___x_5888_;
                            v_isShared_5892_ = v_isSharedCheck_5940_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5889_);
                            lean_dec(v___x_5888_);
                            v___x_5891_ = lean_box(0);
                            v_isShared_5892_ = v_isSharedCheck_5940_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5883_);
                        lean_dec(v_forbidden_5871_);
                        lean_dec(v_mvarId_5870_);
                        v_a_5941_ = lean_ctor_get(v___x_5888_, 0);
                        v_isSharedCheck_5948_ = (!lean_is_exclusive(v___x_5888_)) as u8;
                        if v_isSharedCheck_5948_ == 0 {
                            v___x_5943_ = v___x_5888_;
                            v_isShared_5944_ = v_isSharedCheck_5948_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_5941_);
                            lean_dec(v___x_5888_);
                            v___x_5943_ = lean_box(0);
                            v_isShared_5944_ = v_isSharedCheck_5948_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5883_);
                    lean_dec(v_forbidden_5871_);
                    lean_dec(v_mvarId_5870_);
                    v___x_5949_ = lean_box(0);
                    if v_isShared_5886_ == 0 {
                        lean_ctor_set(v___x_5885_, 0, v___x_5949_);
                        v___x_5951_ = v___x_5885_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_5952_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5952_, 0, v___x_5949_);
                        v___x_5951_ = v_reuseFailAlloc_5952_;
                        state = 13;
                        continue;
                    }
                }
            }
            3 => match lean_obj_tag(v_a_5889_) {
                0 => {
                    lean_dec(v_a_5883_);
                    lean_dec(v_forbidden_5871_);
                    lean_dec(v_mvarId_5870_);
                    v___x_5893_ = lean_box(0);
                    if v_isShared_5892_ == 0 {
                        lean_ctor_set(v___x_5891_, 0, v___x_5893_);
                        v___x_5895_ = v___x_5891_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5896_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5896_, 0, v___x_5893_);
                        v___x_5895_ = v_reuseFailAlloc_5896_;
                        state = 4;
                        continue;
                    }
                }
                1 => {
                    lean_del_object(v___x_5891_);
                    lean_inc(v_mvarId_5870_);
                    v___x_5897_ = l_Lean_Meta_substVars(
                        v_mvarId_5870_,
                        v___y_5878_,
                        v___y_5879_,
                        v___y_5880_,
                        v___y_5881_,
                    );
                    if lean_obj_tag(v___x_5897_) == 0 {
                        v_a_5898_ = lean_ctor_get(v___x_5897_, 0);
                        lean_inc(v_a_5898_);
                        lean_dec_ref_known(v___x_5897_, 1);
                        v___x_5899_ = l_Lean_instBEqMVarId_beq(v_a_5898_, v_mvarId_5870_);
                        if v___x_5899_ == 0 {
                            lean_dec(v_a_5883_);
                            lean_dec(v_mvarId_5870_);
                            v_mvarId_5870_ = v_a_5898_;
                            v_a_5872_ = v___y_5878_;
                            v_a_5873_ = v___y_5879_;
                            v_a_5874_ = v___y_5880_;
                            v_a_5875_ = v___y_5881_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_5898_);
                            lean_dec(v_forbidden_5871_);
                            v___x_5901_ = lean_unsigned_to_nat(16);
                            v___x_5902_ = lean_alloc_ctor(0, 1, (3) as u32);
                            lean_ctor_set(v___x_5902_, 0, v___x_5901_);
                            lean_ctor_set_uint8(
                                v___x_5902_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_5899_,
                            );
                            lean_ctor_set_uint8(
                                v___x_5902_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                v___x_5899_,
                            );
                            v___x_5903_ = (lean_unbox(v_a_5883_) as u8);
                            lean_dec(v_a_5883_);
                            lean_ctor_set_uint8(
                                v___x_5902_,
                                (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                                v___x_5903_,
                            );
                            lean_inc(v_mvarId_5870_);
                            v___x_5904_ = l_Lean_MVarId_contradictionCore(
                                v_mvarId_5870_,
                                v___x_5902_,
                                v___y_5878_,
                                v___y_5879_,
                                v___y_5880_,
                                v___y_5881_,
                            );
                            if lean_obj_tag(v___x_5904_) == 0 {
                                v_a_5905_ = lean_ctor_get(v___x_5904_, 0);
                                v_isSharedCheck_5919_ = (!lean_is_exclusive(v___x_5904_)) as u8;
                                if v_isSharedCheck_5919_ == 0 {
                                    v___x_5907_ = v___x_5904_;
                                    v_isShared_5908_ = v_isSharedCheck_5919_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_5905_);
                                    lean_dec(v___x_5904_);
                                    v___x_5907_ = lean_box(0);
                                    v_isShared_5908_ = v_isSharedCheck_5919_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_mvarId_5870_);
                                v_a_5920_ = lean_ctor_get(v___x_5904_, 0);
                                v_isSharedCheck_5927_ = (!lean_is_exclusive(v___x_5904_)) as u8;
                                if v_isSharedCheck_5927_ == 0 {
                                    v___x_5922_ = v___x_5904_;
                                    v_isShared_5923_ = v_isSharedCheck_5927_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_5920_);
                                    lean_dec(v___x_5904_);
                                    v___x_5922_ = lean_box(0);
                                    v_isShared_5923_ = v_isSharedCheck_5927_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_5883_);
                        lean_dec(v_forbidden_5871_);
                        lean_dec(v_mvarId_5870_);
                        v_a_5928_ = lean_ctor_get(v___x_5897_, 0);
                        v_isSharedCheck_5935_ = (!lean_is_exclusive(v___x_5897_)) as u8;
                        if v_isSharedCheck_5935_ == 0 {
                            v___x_5930_ = v___x_5897_;
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5928_);
                            lean_dec(v___x_5897_);
                            v___x_5930_ = lean_box(0);
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 9;
                            continue;
                        }
                    }
                }
                _ => {
                    lean_del_object(v___x_5891_);
                    lean_dec(v_a_5883_);
                    lean_dec(v_mvarId_5870_);
                    v_fvarId_5936_ = lean_ctor_get(v_a_5889_, 0);
                    lean_inc(v_fvarId_5936_);
                    v_mvarId_5937_ = lean_ctor_get(v_a_5889_, 1);
                    lean_inc(v_mvarId_5937_);
                    lean_dec_ref_known(v_a_5889_, 2);
                    v___x_5938_ = l_Lean_FVarIdSet_insert(v_forbidden_5871_, v_fvarId_5936_);
                    v_mvarId_5870_ = v_mvarId_5937_;
                    v_forbidden_5871_ = v___x_5938_;
                    v_a_5872_ = v___y_5878_;
                    v_a_5873_ = v___y_5879_;
                    v_a_5874_ = v___y_5880_;
                    v_a_5875_ = v___y_5881_;
                    state = 0;
                    continue;
                }
            },
            4 => {
                return v___x_5895_;
            }
            5 => {
                v___x_5909_ = (lean_unbox(v_a_5905_) as u8);
                lean_dec(v_a_5905_);
                if v___x_5909_ == 0 {
                    lean_del_object(v___x_5907_);
                    v___x_5910_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__1_once), _init_l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___closed__1);
                    v___x_5911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5911_, 0, v_mvarId_5870_);
                    v___x_5912_ = l_Lean_indentD(v___x_5911_);
                    v___x_5913_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5913_, 0, v___x_5910_);
                    lean_ctor_set(v___x_5913_, 1, v___x_5912_);
                    v___x_5914_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop_spec__0___redArg(v___x_5913_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_);
                    return v___x_5914_;
                } else {
                    lean_dec(v_mvarId_5870_);
                    v___x_5915_ = lean_box(0);
                    if v_isShared_5908_ == 0 {
                        lean_ctor_set(v___x_5907_, 0, v___x_5915_);
                        v___x_5917_ = v___x_5907_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5918_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5918_, 0, v___x_5915_);
                        v___x_5917_ = v_reuseFailAlloc_5918_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_5917_;
            }
            7 => {
                if v_isShared_5923_ == 0 {
                    v___x_5925_ = v___x_5922_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5926_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5926_, 0, v_a_5920_);
                    v___x_5925_ = v_reuseFailAlloc_5926_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5925_;
            }
            9 => {
                if v_isShared_5931_ == 0 {
                    v___x_5933_ = v___x_5930_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
                    v___x_5933_ = v_reuseFailAlloc_5934_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5933_;
            }
            11 => {
                if v_isShared_5944_ == 0 {
                    v___x_5946_ = v___x_5943_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5947_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5947_, 0, v_a_5941_);
                    v___x_5946_ = v_reuseFailAlloc_5947_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5946_;
            }
            13 => {
                return v___x_5951_;
            }
            14 => {
                if v_isShared_5957_ == 0 {
                    v___x_5959_ = v___x_5956_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5960_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5960_, 0, v_a_5954_);
                    v___x_5959_ = v_reuseFailAlloc_5960_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop___boxed(
    mut v_mvarId_5972_: *mut LeanObject,
    mut v_forbidden_5973_: *mut LeanObject,
    mut v_a_5974_: *mut LeanObject,
    mut v_a_5975_: *mut LeanObject,
    mut v_a_5976_: *mut LeanObject,
    mut v_a_5977_: *mut LeanObject,
    mut v_a_5978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5979_: *mut LeanObject = core::ptr::null_mut();
    v_res_5979_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop(
        v_mvarId_5972_,
        v_forbidden_5973_,
        v_a_5974_,
        v_a_5975_,
        v_a_5976_,
        v_a_5977_,
    );
    lean_dec(v_a_5977_);
    lean_dec_ref(v_a_5976_);
    lean_dec(v_a_5975_);
    lean_dec_ref(v_a_5974_);
    return v_res_5979_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop_spec__0(
    mut v_00_u03b1_5980_: *mut LeanObject,
    mut v_msg_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
    mut v___y_5984_: *mut LeanObject,
    mut v___y_5985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    v___x_5987_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop_spec__0___redArg(v_msg_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_);
    return v___x_5987_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop_spec__0___boxed(
    mut v_00_u03b1_5988_: *mut LeanObject,
    mut v_msg_5989_: *mut LeanObject,
    mut v___y_5990_: *mut LeanObject,
    mut v___y_5991_: *mut LeanObject,
    mut v___y_5992_: *mut LeanObject,
    mut v___y_5993_: *mut LeanObject,
    mut v___y_5994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5995_: *mut LeanObject = core::ptr::null_mut();
    v_res_5995_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop_spec__0(v_00_u03b1_5988_, v_msg_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
    lean_dec(v___y_5993_);
    lean_dec_ref(v___y_5992_);
    lean_dec(v___y_5991_);
    lean_dec_ref(v___y_5990_);
    return v_res_5995_;
}
pub unsafe fn _init_l_Lean_Meta_Match_solveOverlap___closed__1() -> *mut LeanObject {
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    v___x_5997_ = l_Lean_Meta_Match_solveOverlap___closed__0;
    v___x_5998_ = l_Lean_stringToMessageData(v___x_5997_);
    return v___x_5998_;
}
pub unsafe fn _init_l_Lean_Meta_Match_solveOverlap___closed__3() -> *mut LeanObject {
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    v___x_6000_ = l_Lean_Meta_Match_solveOverlap___closed__2;
    v___x_6001_ = l_Lean_stringToMessageData(v___x_6000_);
    return v___x_6001_;
}
pub unsafe fn _init_l_Lean_Meta_Match_solveOverlap___closed__5() -> *mut LeanObject {
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    v___x_6003_ = l_Lean_Meta_Match_solveOverlap___closed__4;
    v___x_6004_ = l_Lean_stringToMessageData(v___x_6003_);
    return v___x_6004_;
}
pub unsafe fn l_Lean_Meta_Match_solveOverlap(
    mut v_mvarId_6005_: *mut LeanObject,
    mut v_a_6006_: *mut LeanObject,
    mut v_a_6007_: *mut LeanObject,
    mut v_a_6008_: *mut LeanObject,
    mut v_a_6009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6013_: u8 = 0;
    let mut v___x_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6027_: u8 = 0;
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6031_: u8 = 0;
    let mut v_cls_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: u8 = 0;
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_6037_: u8 = 0;
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6057_: u8 = 0;
    let mut v___x_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_6011_ = lean_ctor_get(v_a_6008_, 2);
                v_inheritedTraceOptions_6012_ = lean_ctor_get(v_a_6008_, 13);
                v_hasTrace_6013_ = lean_ctor_get_uint8(
                    v_options_6011_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v___x_6014_ = lean_box(1);
                if v_hasTrace_6013_ == 0 {
                    v___y_6016_ = v_a_6006_;
                    v___y_6017_ = v_a_6007_;
                    v___y_6018_ = v_a_6008_;
                    v___y_6019_ = v_a_6009_;
                    state = 1;
                    continue;
                } else {
                    v_cls_6032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__4;
                    v___x_6033_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__2_spec__3_spec__5_spec__6___closed__7);
                    v___x_6034_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6012_,
                        v_options_6011_,
                        v___x_6033_,
                    );
                    if v___x_6034_ == 0 {
                        v___y_6016_ = v_a_6006_;
                        v___y_6017_ = v_a_6007_;
                        v___y_6018_ = v_a_6008_;
                        v___y_6019_ = v_a_6009_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_mvarId_6005_);
                        v___x_6035_ = l_Lean_MVarId_getDecl(
                            v_mvarId_6005_,
                            v_a_6006_,
                            v_a_6007_,
                            v_a_6008_,
                            v_a_6009_,
                        );
                        if lean_obj_tag(v___x_6035_) == 0 {
                            v_a_6036_ = lean_ctor_get(v___x_6035_, 0);
                            lean_inc(v_a_6036_);
                            lean_dec_ref_known(v___x_6035_, 1);
                            v_kind_6037_ = lean_ctor_get_uint8(
                                v_a_6036_,
                                (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                            );
                            lean_dec(v_a_6036_);
                            v___x_6038_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Match_solveOverlap___closed__1),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Match_solveOverlap___closed__1_once
                                ),
                                _init_l_Lean_Meta_Match_solveOverlap___closed__1,
                            );
                            lean_inc_n(v_mvarId_6005_, 2);
                            v___x_6039_ = l_Lean_mkMVar(v_mvarId_6005_);
                            v___x_6040_ = l_Lean_MessageData_ofExpr(v___x_6039_);
                            v___x_6041_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6041_, 0, v___x_6038_);
                            lean_ctor_set(v___x_6041_, 1, v___x_6040_);
                            v___x_6042_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Match_solveOverlap___closed__3),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Match_solveOverlap___closed__3_once
                                ),
                                _init_l_Lean_Meta_Match_solveOverlap___closed__3,
                            );
                            v___x_6043_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6043_, 0, v___x_6041_);
                            lean_ctor_set(v___x_6043_, 1, v___x_6042_);
                            v___x_6044_ = lean_unsigned_to_nat(0);
                            v___x_6045_ =
                                l_Lean_instReprMetavarKind_repr(v_kind_6037_, v___x_6044_);
                            v___x_6046_ = l_Lean_MessageData_ofFormat(v___x_6045_);
                            v___x_6047_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6047_, 0, v___x_6043_);
                            lean_ctor_set(v___x_6047_, 1, v___x_6046_);
                            v___x_6048_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Meta_Match_solveOverlap___closed__5),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Match_solveOverlap___closed__5_once
                                ),
                                _init_l_Lean_Meta_Match_solveOverlap___closed__5,
                            );
                            v___x_6049_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6049_, 0, v___x_6047_);
                            lean_ctor_set(v___x_6049_, 1, v___x_6048_);
                            v___x_6050_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_6050_, 0, v_mvarId_6005_);
                            v___x_6051_ = l_Lean_indentD(v___x_6050_);
                            v___x_6052_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_6052_, 0, v___x_6049_);
                            lean_ctor_set(v___x_6052_, 1, v___x_6051_);
                            v___x_6053_ = l_Lean_addTrace___at___00__private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_injectionAny_spec__1(v_cls_6032_, v___x_6052_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_);
                            if lean_obj_tag(v___x_6053_) == 0 {
                                lean_dec_ref_known(v___x_6053_, 1);
                                v___y_6016_ = v_a_6006_;
                                v___y_6017_ = v_a_6007_;
                                v___y_6018_ = v_a_6008_;
                                v___y_6019_ = v_a_6009_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_mvarId_6005_);
                                return v___x_6053_;
                            }
                        } else {
                            lean_dec(v_mvarId_6005_);
                            v_a_6054_ = lean_ctor_get(v___x_6035_, 0);
                            v_isSharedCheck_6061_ = (!lean_is_exclusive(v___x_6035_)) as u8;
                            if v_isSharedCheck_6061_ == 0 {
                                v___x_6056_ = v___x_6035_;
                                v_isShared_6057_ = v_isSharedCheck_6061_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_6054_);
                                lean_dec(v___x_6035_);
                                v___x_6056_ = lean_box(0);
                                v_isShared_6057_ = v_isSharedCheck_6061_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6020_ = l_Lean_MVarId_intros(
                    v_mvarId_6005_,
                    v___y_6016_,
                    v___y_6017_,
                    v___y_6018_,
                    v___y_6019_,
                );
                if lean_obj_tag(v___x_6020_) == 0 {
                    v_a_6021_ = lean_ctor_get(v___x_6020_, 0);
                    lean_inc(v_a_6021_);
                    lean_dec_ref_known(v___x_6020_, 1);
                    v_snd_6022_ = lean_ctor_get(v_a_6021_, 1);
                    lean_inc(v_snd_6022_);
                    lean_dec(v_a_6021_);
                    v___x_6023_ = l___private_Lean_Meta_Match_SolveOverlap_0__Lean_Meta_Match_solveOverlap_loop(v_snd_6022_, v___x_6014_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_);
                    return v___x_6023_;
                } else {
                    v_a_6024_ = lean_ctor_get(v___x_6020_, 0);
                    v_isSharedCheck_6031_ = (!lean_is_exclusive(v___x_6020_)) as u8;
                    if v_isSharedCheck_6031_ == 0 {
                        v___x_6026_ = v___x_6020_;
                        v_isShared_6027_ = v_isSharedCheck_6031_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6024_);
                        lean_dec(v___x_6020_);
                        v___x_6026_ = lean_box(0);
                        v_isShared_6027_ = v_isSharedCheck_6031_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6027_ == 0 {
                    v___x_6029_ = v___x_6026_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6030_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6024_);
                    v___x_6029_ = v_reuseFailAlloc_6030_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6029_;
            }
            4 => {
                if v_isShared_6057_ == 0 {
                    v___x_6059_ = v___x_6056_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6060_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6060_, 0, v_a_6054_);
                    v___x_6059_ = v_reuseFailAlloc_6060_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_solveOverlap___boxed(
    mut v_mvarId_6062_: *mut LeanObject,
    mut v_a_6063_: *mut LeanObject,
    mut v_a_6064_: *mut LeanObject,
    mut v_a_6065_: *mut LeanObject,
    mut v_a_6066_: *mut LeanObject,
    mut v_a_6067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6068_: *mut LeanObject = core::ptr::null_mut();
    v_res_6068_ =
        l_Lean_Meta_Match_solveOverlap(v_mvarId_6062_, v_a_6063_, v_a_6064_, v_a_6065_, v_a_6066_);
    lean_dec(v_a_6066_);
    lean_dec_ref(v_a_6065_);
    lean_dec(v_a_6064_);
    lean_dec_ref(v_a_6063_);
    return v_res_6068_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_SolveOverlap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_SolveOverlap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_SolveOverlap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_SolveOverlap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_SolveOverlap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Match_SolveOverlap(builtin);
}
