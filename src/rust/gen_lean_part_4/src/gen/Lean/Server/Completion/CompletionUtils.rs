// Lean compiler output
// Module: Lean.Server.Completion.CompletionUtils
// Imports: Lean.Meta.WHNF
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr,
    lean_nat_sub, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_get_byte_fast, lean_string_utf8_at_end, lean_string_utf8_byte_size,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint8_add, lean_uint8_dec_eq,
    lean_uint8_dec_le, lean_uint8_land, lean_uint32_add, lean_uint32_dec_eq, lean_uint32_dec_le,
    lean_uint64_of_nat, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le,
    lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop, l_Array_eraseIdx___redArg,
    l_Array_instInhabited,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_replacePrefix;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::{
    l_Lean_Name_getNumParts, l_Lean_Name_getPrefix, l_Lean_Name_lt,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::l_Lean_EnvExtension_modifyState___redArg;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_getAppFn, l_Lean_Expr_hasMVar, l_Lean_Expr_isForall};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux;
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_unfoldDefinition_x3f,
    l_Lean_Meta_whnfCoreUnfoldingAnnotations, runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Structure::{
    l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f,
    l_Lean_getStructureParentInfo, l_Lean_isStructure, l_Lean_structureResolutionExt,
};
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10___closed__0_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__1_value) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__3_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__2_value) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__String_charactersIn_go(
    mut v_a_2307_: *mut leanh::LeanObject,
    mut v_b_2308_: *mut leanh::LeanObject,
    mut v_aPos_2309_: *mut leanh::LeanObject,
    mut v_bPos_2310_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2311_: u8 = 0;
    let mut v___x_2312_: u8 = 0;
    let mut v_ac_2313_: u32 = 0;
    let mut v_bc_2314_: u32 = 0;
    let mut v_bPos_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2317_: u32 = 0;
    let mut v___y_2318_: u32 = 0;
    let mut v___x_2319_: u8 = 0;
    let mut v_aPos_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2324_: u32 = 0;
    let mut v___x_2325_: u32 = 0;
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2327_: u32 = 0;
    let mut v___x_2328_: u8 = 0;
    let mut v___x_2329_: u32 = 0;
    let mut v___x_2330_: u32 = 0;
    let mut v___x_2331_: u32 = 0;
    let mut v___x_2332_: u8 = 0;
    let mut v___x_2333_: u32 = 0;
    let mut v___x_2334_: u8 = 0;
    let mut v___x_2335_: u32 = 0;
    let mut v___x_2336_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2311_ = lean_string_utf8_at_end(v_a_2307_, v_aPos_2309_);
                if v___x_2311_ == 0 {
                    v___x_2312_ = lean_string_utf8_at_end(v_b_2308_, v_bPos_2310_);
                    if v___x_2312_ == 0 {
                        v_ac_2313_ = lean_string_utf8_get_fast(v_a_2307_, v_aPos_2309_);
                        v_bc_2314_ = lean_string_utf8_get_fast(v_b_2308_, v_bPos_2310_);
                        v_bPos_2315_ = lean_string_utf8_next_fast(v_b_2308_, v_bPos_2310_);
                        leanh::lean_dec(v_bPos_2310_);
                        v___x_2331_ = 65;
                        v___x_2332_ = lean_uint32_dec_le(v___x_2331_, v_ac_2313_);
                        if v___x_2332_ == 0 {
                            v___y_2324_ = v_ac_2313_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2333_ = 90;
                            v___x_2334_ = lean_uint32_dec_le(v_ac_2313_, v___x_2333_);
                            if v___x_2334_ == 0 {
                                v___y_2324_ = v_ac_2313_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2335_ = 32;
                                v___x_2336_ = lean_uint32_add(v_ac_2313_, v___x_2335_);
                                v___y_2324_ = v___x_2336_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_bPos_2310_);
                        leanh::lean_dec(v_aPos_2309_);
                        return v___x_2311_;
                    }
                } else {
                    leanh::lean_dec(v_bPos_2310_);
                    leanh::lean_dec(v_aPos_2309_);
                    return v___x_2311_;
                }
            }
            1 => {
                v___x_2319_ = lean_uint32_dec_eq(v___y_2317_, v___y_2318_);
                if v___x_2319_ == 0 {
                    v_bPos_2310_ = v_bPos_2315_;
                    state = 0;
                    continue;
                } else {
                    v_aPos_2321_ = lean_string_utf8_next_fast(v_a_2307_, v_aPos_2309_);
                    leanh::lean_dec(v_aPos_2309_);
                    v_aPos_2309_ = v_aPos_2321_;
                    v_bPos_2310_ = v_bPos_2315_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_2325_ = 65;
                v___x_2326_ = lean_uint32_dec_le(v___x_2325_, v_bc_2314_);
                if v___x_2326_ == 0 {
                    v___y_2317_ = v___y_2324_;
                    v___y_2318_ = v_bc_2314_;
                    state = 1;
                    continue;
                } else {
                    v___x_2327_ = 90;
                    v___x_2328_ = lean_uint32_dec_le(v_bc_2314_, v___x_2327_);
                    if v___x_2328_ == 0 {
                        v___y_2317_ = v___y_2324_;
                        v___y_2318_ = v_bc_2314_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2329_ = 32;
                        v___x_2330_ = lean_uint32_add(v_bc_2314_, v___x_2329_);
                        v___y_2317_ = v___y_2324_;
                        v___y_2318_ = v___x_2330_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__String_charactersIn_go___boxed(
    mut v_a_2337_: *mut leanh::LeanObject,
    mut v_b_2338_: *mut leanh::LeanObject,
    mut v_aPos_2339_: *mut leanh::LeanObject,
    mut v_bPos_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2341_: u8 = 0;
    let mut v_r_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l___private_Lean_Server_Completion_CompletionUtils_0__String_charactersIn_go(
        v_a_2337_,
        v_b_2338_,
        v_aPos_2339_,
        v_bPos_2340_,
    );
    leanh::lean_dec_ref(v_b_2338_);
    leanh::lean_dec_ref(v_a_2337_);
    v_r_2342_ = leanh::lean_box((v_res_2341_) as usize);
    return v_r_2342_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__String_charactersIn_goFastScalar(
    mut v_a_2343_: *mut leanh::LeanObject,
    mut v_b_2344_: *mut leanh::LeanObject,
    mut v_aPos_2345_: *mut leanh::LeanObject,
    mut v_bPos_2346_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: u8 = 0;
    let mut v___x_2349_: u8 = 0;
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: u8 = 0;
    let mut v_aByte_2352_: u8 = 0;
    let mut v___x_2353_: u8 = 0;
    let mut v___x_2354_: u8 = 0;
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: u8 = 0;
    let mut v_bByte_2358_: u8 = 0;
    let mut v___x_2359_: u8 = 0;
    let mut v___x_2360_: u8 = 0;
    let mut v___x_2361_: u8 = 0;
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bPos_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2365_: u8 = 0;
    let mut v___y_2366_: u8 = 0;
    let mut v___x_2367_: u8 = 0;
    let mut v_aPos_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2372_: u8 = 0;
    let mut v___y_2373_: u8 = 0;
    let mut v___x_2374_: u8 = 0;
    let mut v___x_2375_: u8 = 0;
    let mut v___y_2377_: u8 = 0;
    let mut v___x_2378_: u8 = 0;
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: u8 = 0;
    let mut v___x_2381_: u8 = 0;
    let mut v___y_2383_: u8 = 0;
    let mut v___x_2384_: u8 = 0;
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: u8 = 0;
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: u8 = 0;
    let mut v___x_2389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2347_ = lean_string_utf8_byte_size(v_a_2343_);
                v___x_2348_ = lean_nat_dec_lt(v_aPos_2345_, v___x_2347_);
                if v___x_2348_ == 0 {
                    leanh::lean_dec(v_bPos_2346_);
                    leanh::lean_dec(v_aPos_2345_);
                    v___x_2349_ = 1;
                    return v___x_2349_;
                } else {
                    v___x_2350_ = lean_string_utf8_byte_size(v_b_2344_);
                    v___x_2351_ = lean_nat_dec_lt(v_bPos_2346_, v___x_2350_);
                    if v___x_2351_ == 0 {
                        leanh::lean_dec(v_bPos_2346_);
                        leanh::lean_dec(v_aPos_2345_);
                        return v___x_2351_;
                    } else {
                        leanh::lean_inc(v_aPos_2345_);
                        v_aByte_2352_ = lean_string_get_byte_fast(v_a_2343_, v_aPos_2345_);
                        v___x_2353_ = 128;
                        v___x_2354_ = lean_uint8_land(v_aByte_2352_, v___x_2353_);
                        v___x_2355_ = 0;
                        v___x_2356_ = lean_uint8_dec_eq(v___x_2354_, v___x_2355_);
                        if v___x_2356_ == 0 {
                            v___x_2357_ = l___private_Lean_Server_Completion_CompletionUtils_0__String_charactersIn_go(v_a_2343_, v_b_2344_, v_aPos_2345_, v_bPos_2346_);
                            return v___x_2357_;
                        } else {
                            leanh::lean_inc(v_bPos_2346_);
                            v_bByte_2358_ = lean_string_get_byte_fast(v_b_2344_, v_bPos_2346_);
                            v___x_2359_ = lean_uint8_land(v_bByte_2358_, v___x_2353_);
                            v___x_2360_ = lean_uint8_dec_eq(v___x_2359_, v___x_2355_);
                            if v___x_2360_ == 0 {
                                v___x_2361_ = l___private_Lean_Server_Completion_CompletionUtils_0__String_charactersIn_go(v_a_2343_, v_b_2344_, v_aPos_2345_, v_bPos_2346_);
                                return v___x_2361_;
                            } else {
                                v___x_2362_ = leanh::lean_unsigned_to_nat(1);
                                v_bPos_2363_ = lean_nat_add(v_bPos_2346_, v___x_2362_);
                                leanh::lean_dec(v_bPos_2346_);
                                v___x_2386_ = 65;
                                v___x_2387_ = lean_uint8_dec_le(v___x_2386_, v_aByte_2352_);
                                if v___x_2387_ == 0 {
                                    v___y_2383_ = v___x_2387_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_2388_ = 90;
                                    v___x_2389_ = lean_uint8_dec_le(v_aByte_2352_, v___x_2388_);
                                    v___y_2383_ = v___x_2389_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2367_ = lean_uint8_dec_eq(v___y_2365_, v___y_2366_);
                if v___x_2367_ == 0 {
                    v_bPos_2346_ = v_bPos_2363_;
                    state = 0;
                    continue;
                } else {
                    v_aPos_2369_ = lean_nat_add(v_aPos_2345_, v___x_2362_);
                    leanh::lean_dec(v_aPos_2345_);
                    v_aPos_2345_ = v_aPos_2369_;
                    v_bPos_2346_ = v_bPos_2363_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_2373_ == 0 {
                    v___y_2365_ = v___y_2372_;
                    v___y_2366_ = v_bByte_2358_;
                    state = 1;
                    continue;
                } else {
                    v___x_2374_ = 32;
                    v___x_2375_ = lean_uint8_add(v_bByte_2358_, v___x_2374_);
                    v___y_2365_ = v___y_2372_;
                    v___y_2366_ = v___x_2375_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2378_ = 65;
                v___x_2379_ = lean_uint8_dec_le(v___x_2378_, v_bByte_2358_);
                if v___x_2379_ == 0 {
                    v___y_2372_ = v___y_2377_;
                    v___y_2373_ = v___x_2379_;
                    state = 2;
                    continue;
                } else {
                    v___x_2380_ = 90;
                    v___x_2381_ = lean_uint8_dec_le(v_bByte_2358_, v___x_2380_);
                    v___y_2372_ = v___y_2377_;
                    v___y_2373_ = v___x_2381_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                if v___y_2383_ == 0 {
                    v___y_2377_ = v_aByte_2352_;
                    state = 3;
                    continue;
                } else {
                    v___x_2384_ = 32;
                    v___x_2385_ = lean_uint8_add(v_aByte_2352_, v___x_2384_);
                    v___y_2377_ = v___x_2385_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__String_charactersIn_goFastScalar___boxed(
    mut v_a_2390_: *mut leanh::LeanObject,
    mut v_b_2391_: *mut leanh::LeanObject,
    mut v_aPos_2392_: *mut leanh::LeanObject,
    mut v_bPos_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2394_: u8 = 0;
    let mut v_r_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2394_ =
        l___private_Lean_Server_Completion_CompletionUtils_0__String_charactersIn_goFastScalar(
            v_a_2390_,
            v_b_2391_,
            v_aPos_2392_,
            v_bPos_2393_,
        );
    leanh::lean_dec_ref(v_b_2391_);
    leanh::lean_dec_ref(v_a_2390_);
    v_r_2395_ = leanh::lean_box((v_res_2394_) as usize);
    return v_r_2395_;
}
pub unsafe fn l_String_charactersIn(
    mut v_a_2396_: *mut leanh::LeanObject,
    mut v_b_2397_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: u8 = 0;
    v___x_2398_ = leanh::lean_unsigned_to_nat(0);
    v___x_2399_ =
        l___private_Lean_Server_Completion_CompletionUtils_0__String_charactersIn_goFastScalar(
            v_a_2396_,
            v_b_2397_,
            v___x_2398_,
            v___x_2398_,
        );
    return v___x_2399_;
}
pub unsafe fn l_String_charactersIn___boxed(
    mut v_a_2400_: *mut leanh::LeanObject,
    mut v_b_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2402_: u8 = 0;
    let mut v_r_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2402_ = l_String_charactersIn(v_a_2400_, v_b_2401_);
    leanh::lean_dec_ref(v_b_2401_);
    leanh::lean_dec_ref(v_a_2400_);
    v_r_2403_ = leanh::lean_box((v_res_2402_) as usize);
    return v_r_2403_;
}
pub unsafe fn l_Lean_Server_Completion_HoverInfo_ctorIdx(
    mut v_x_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2404_) == 0 {
        let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2405_ = leanh::lean_unsigned_to_nat(0);
        return v___x_2405_;
    } else {
        let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2406_ = leanh::lean_unsigned_to_nat(1);
        return v___x_2406_;
    }
}
pub unsafe fn l_Lean_Server_Completion_HoverInfo_ctorIdx___boxed(
    mut v_x_2407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ = l_Lean_Server_Completion_HoverInfo_ctorIdx(v_x_2407_);
    leanh::lean_dec(v_x_2407_);
    return v_res_2408_;
}
pub unsafe fn l_Lean_Server_Completion_HoverInfo_ctorElim___redArg(
    mut v_t_2409_: *mut leanh::LeanObject,
    mut v_k_2410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_2409_) == 0 {
        return v_k_2410_;
    } else {
        let mut v_delta_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_delta_2411_ = leanh::lean_ctor_get(v_t_2409_, 0);
        leanh::lean_inc(v_delta_2411_);
        leanh::lean_dec_ref_known(v_t_2409_, 1);
        v___x_2412_ = leanh::lean_apply_1(v_k_2410_, v_delta_2411_);
        return v___x_2412_;
    }
}
pub unsafe fn l_Lean_Server_Completion_HoverInfo_ctorElim(
    mut v_motive_2413_: *mut leanh::LeanObject,
    mut v_ctorIdx_2414_: *mut leanh::LeanObject,
    mut v_t_2415_: *mut leanh::LeanObject,
    mut v_h_2416_: *mut leanh::LeanObject,
    mut v_k_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2418_ = l_Lean_Server_Completion_HoverInfo_ctorElim___redArg(v_t_2415_, v_k_2417_);
    return v___x_2418_;
}
pub unsafe fn l_Lean_Server_Completion_HoverInfo_ctorElim___boxed(
    mut v_motive_2419_: *mut leanh::LeanObject,
    mut v_ctorIdx_2420_: *mut leanh::LeanObject,
    mut v_t_2421_: *mut leanh::LeanObject,
    mut v_h_2422_: *mut leanh::LeanObject,
    mut v_k_2423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ = l_Lean_Server_Completion_HoverInfo_ctorElim(
        v_motive_2419_,
        v_ctorIdx_2420_,
        v_t_2421_,
        v_h_2422_,
        v_k_2423_,
    );
    leanh::lean_dec(v_ctorIdx_2420_);
    return v_res_2424_;
}
pub unsafe fn l_Lean_Server_Completion_HoverInfo_after_elim___redArg(
    mut v_t_2425_: *mut leanh::LeanObject,
    mut v_after_2426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = l_Lean_Server_Completion_HoverInfo_ctorElim___redArg(v_t_2425_, v_after_2426_);
    return v___x_2427_;
}
pub unsafe fn l_Lean_Server_Completion_HoverInfo_after_elim(
    mut v_motive_2428_: *mut leanh::LeanObject,
    mut v_t_2429_: *mut leanh::LeanObject,
    mut v_h_2430_: *mut leanh::LeanObject,
    mut v_after_2431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2432_ = l_Lean_Server_Completion_HoverInfo_ctorElim___redArg(v_t_2429_, v_after_2431_);
    return v___x_2432_;
}
pub unsafe fn l_Lean_Server_Completion_HoverInfo_inside_elim___redArg(
    mut v_t_2433_: *mut leanh::LeanObject,
    mut v_inside_2434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2435_ = l_Lean_Server_Completion_HoverInfo_ctorElim___redArg(v_t_2433_, v_inside_2434_);
    return v___x_2435_;
}
pub unsafe fn l_Lean_Server_Completion_HoverInfo_inside_elim(
    mut v_motive_2436_: *mut leanh::LeanObject,
    mut v_t_2437_: *mut leanh::LeanObject,
    mut v_h_2438_: *mut leanh::LeanObject,
    mut v_inside_2439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2440_ = l_Lean_Server_Completion_HoverInfo_ctorElim___redArg(v_t_2437_, v_inside_2439_);
    return v___x_2440_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenInOpenNamespace(
    mut v_id_2441_: *mut leanh::LeanObject,
    mut v_openNamespace_2442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2443_: u8 = 0;
    v___x_2443_ = lean_name_eq(v_openNamespace_2442_, v_id_2441_);
    if v___x_2443_ == 0 {
        let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2444_ = leanh::lean_box(0);
        v___x_2445_ = l_Lean_Name_replacePrefix(v_id_2441_, v_openNamespace_2442_, v___x_2444_);
        return v___x_2445_;
    } else {
        return v_id_2441_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenInOpenNamespace___boxed(
    mut v_id_2446_: *mut leanh::LeanObject,
    mut v_openNamespace_2447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2448_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenInOpenNamespace(v_id_2446_, v_openNamespace_2447_);
    leanh::lean_dec(v_openNamespace_2447_);
    return v_res_2448_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenInCurrentNamespace(
    mut v_id_2449_: *mut leanh::LeanObject,
    mut v_currentNamespace_2450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_maybeShortened_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: u8 = 0;
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_currentNamespace_2450_) == 0 {
                    return v_id_2449_;
                } else {
                    leanh::lean_inc(v_id_2449_);
                    v_maybeShortened_2451_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenInOpenNamespace(v_id_2449_, v_currentNamespace_2450_);
                    v___x_2452_ = lean_name_eq(v_maybeShortened_2451_, v_id_2449_);
                    if v___x_2452_ == 0 {
                        leanh::lean_dec(v_currentNamespace_2450_);
                        leanh::lean_dec(v_id_2449_);
                        return v_maybeShortened_2451_;
                    } else {
                        leanh::lean_dec(v_maybeShortened_2451_);
                        v___x_2453_ = l_Lean_Name_getPrefix(v_currentNamespace_2450_);
                        leanh::lean_dec(v_currentNamespace_2450_);
                        v_currentNamespace_2450_ = v___x_2453_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__0(
    mut v_a_2455_: *mut leanh::LeanObject,
    mut v_x_2456_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2457_: u8 = 0;
    let mut v_head_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2456_) == 0 {
                    v___x_2457_ = 0;
                    return v___x_2457_;
                } else {
                    v_head_2458_ = leanh::lean_ctor_get(v_x_2456_, 0);
                    v_tail_2459_ = leanh::lean_ctor_get(v_x_2456_, 1);
                    v___x_2460_ = lean_name_eq(v_a_2455_, v_head_2458_);
                    if v___x_2460_ == 0 {
                        v_x_2456_ = v_tail_2459_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2460_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__0___boxed(
    mut v_a_2462_: *mut leanh::LeanObject,
    mut v_x_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2464_: u8 = 0;
    let mut v_r_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2464_ =
        l_List_elem___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__0(
            v_a_2462_, v_x_2463_,
        );
    leanh::lean_dec(v_x_2463_);
    leanh::lean_dec(v_a_2462_);
    v_r_2465_ = leanh::lean_box((v_res_2464_) as usize);
    return v_r_2465_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__1___redArg(
    mut v_id_2466_: *mut leanh::LeanObject,
    mut v_as_x27_2467_: *mut leanh::LeanObject,
    mut v_b_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: u8 = 0;
    let mut v_ns_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_except_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: u8 = 0;
    let mut v_id_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_2467_) == 0 {
                    leanh::lean_dec(v_id_2466_);
                    return v_b_2468_;
                } else {
                    v_head_2469_ = leanh::lean_ctor_get(v_as_x27_2467_, 0);
                    v_tail_2470_ = leanh::lean_ctor_get(v_as_x27_2467_, 1);
                    if leanh::lean_obj_tag(v_head_2469_) == 0 {
                        v_ns_2478_ = leanh::lean_ctor_get(v_head_2469_, 0);
                        v_except_2479_ = leanh::lean_ctor_get(v_head_2469_, 1);
                        leanh::lean_inc(v_id_2466_);
                        v___x_2480_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenInOpenNamespace(v_id_2466_, v_ns_2478_);
                        v___x_2481_ = l_List_elem___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__0(v___x_2480_, v_except_2479_);
                        if v___x_2481_ == 0 {
                            v_val_2472_ = v___x_2480_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2480_);
                            v_as_x27_2467_ = v_tail_2470_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_id_2483_ = leanh::lean_ctor_get(v_head_2469_, 0);
                        v_declName_2484_ = leanh::lean_ctor_get(v_head_2469_, 1);
                        v___x_2485_ = lean_name_eq(v_declName_2484_, v_id_2466_);
                        if v___x_2485_ == 0 {
                            v_as_x27_2467_ = v_tail_2470_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_inc(v_id_2483_);
                            v_val_2472_ = v_id_2483_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2473_ = l_Lean_Name_getNumParts(v_val_2472_);
                v___x_2474_ = l_Lean_Name_getNumParts(v_b_2468_);
                v___x_2475_ = lean_nat_dec_lt(v___x_2473_, v___x_2474_);
                leanh::lean_dec(v___x_2474_);
                leanh::lean_dec(v___x_2473_);
                if v___x_2475_ == 0 {
                    leanh::lean_dec(v_val_2472_);
                    v_as_x27_2467_ = v_tail_2470_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_b_2468_);
                    v_as_x27_2467_ = v_tail_2470_;
                    v_b_2468_ = v_val_2472_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__1___redArg___boxed(
    mut v_id_2487_: *mut leanh::LeanObject,
    mut v_as_x27_2488_: *mut leanh::LeanObject,
    mut v_b_2489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2490_ = l_List_forIn_x27_loop___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__1___redArg(v_id_2487_, v_as_x27_2488_, v_b_2489_);
    leanh::lean_dec(v_as_x27_2488_);
    return v_res_2490_;
}
pub unsafe fn l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(
    mut v_currNamespace_2491_: *mut leanh::LeanObject,
    mut v_openDecls_2492_: *mut leanh::LeanObject,
    mut v_id_2493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_minimized_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_id_2493_);
    v_minimized_2494_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_minimizeGlobalIdentifierInContext_shortenInCurrentNamespace(v_id_2493_, v_currNamespace_2491_);
    v___x_2495_ = l_List_forIn_x27_loop___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__1___redArg(v_id_2493_, v_openDecls_2492_, v_minimized_2494_);
    return v___x_2495_;
}
pub unsafe fn l_Lean_Server_Completion_minimizeGlobalIdentifierInContext___boxed(
    mut v_currNamespace_2496_: *mut leanh::LeanObject,
    mut v_openDecls_2497_: *mut leanh::LeanObject,
    mut v_id_2498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2499_ = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(
        v_currNamespace_2496_,
        v_openDecls_2497_,
        v_id_2498_,
    );
    leanh::lean_dec(v_openDecls_2497_);
    return v_res_2499_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__1(
    mut v_id_2500_: *mut leanh::LeanObject,
    mut v_as_2501_: *mut leanh::LeanObject,
    mut v_as_x27_2502_: *mut leanh::LeanObject,
    mut v_b_2503_: *mut leanh::LeanObject,
    mut v_a_2504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2505_ = l_List_forIn_x27_loop___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__1___redArg(v_id_2500_, v_as_x27_2502_, v_b_2503_);
    return v___x_2505_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__1___boxed(
    mut v_id_2506_: *mut leanh::LeanObject,
    mut v_as_2507_: *mut leanh::LeanObject,
    mut v_as_x27_2508_: *mut leanh::LeanObject,
    mut v_b_2509_: *mut leanh::LeanObject,
    mut v_a_2510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2511_ = l_List_forIn_x27_loop___at___00Lean_Server_Completion_minimizeGlobalIdentifierInContext_spec__1(v_id_2506_, v_as_2507_, v_as_x27_2508_, v_b_2509_, v_a_2510_);
    leanh::lean_dec(v_as_x27_2508_);
    leanh::lean_dec(v_as_2507_);
    return v_res_2511_;
}
pub unsafe fn l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(
    mut v_e_2512_: *mut leanh::LeanObject,
    mut v_a_2513_: *mut leanh::LeanObject,
    mut v_a_2514_: *mut leanh::LeanObject,
    mut v_a_2515_: *mut leanh::LeanObject,
    mut v_a_2516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2518_: u8 = 0;
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: u8 = 0;
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2530_: u8 = 0;
    let mut v_unused_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: u8 = 0;
    let mut v___x_2533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2518_ = 0;
                v___x_2519_ = l_Lean_Meta_unfoldDefinition_x3f(
                    v_e_2512_,
                    v___x_2518_,
                    v_a_2513_,
                    v_a_2514_,
                    v_a_2515_,
                    v_a_2516_,
                );
                if leanh::lean_obj_tag(v___x_2519_) == 0 {
                    return v___x_2519_;
                } else {
                    v_a_2520_ = leanh::lean_ctor_get(v___x_2519_, 0);
                    leanh::lean_inc(v_a_2520_);
                    v___x_2532_ = l_Lean_Exception_isInterrupt(v_a_2520_);
                    if v___x_2532_ == 0 {
                        v___x_2533_ = l_Lean_Exception_isRuntime(v_a_2520_);
                        v___y_2522_ = v___x_2533_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2520_);
                        v___y_2522_ = v___x_2532_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2522_ == 0 {
                    v_isSharedCheck_2530_ = (!leanh::lean_is_exclusive(v___x_2519_)) as u8;
                    if v_isSharedCheck_2530_ == 0 {
                        v_unused_2531_ = leanh::lean_ctor_get(v___x_2519_, 0);
                        leanh::lean_dec(v_unused_2531_);
                        v___x_2524_ = v___x_2519_;
                        v_isShared_2525_ = v_isSharedCheck_2530_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2519_);
                        v___x_2524_ = leanh::lean_box(0);
                        v_isShared_2525_ = v_isSharedCheck_2530_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_2519_;
                }
            }
            2 => {
                v___x_2526_ = leanh::lean_box(0);
                if v_isShared_2525_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2524_, 0);
                    leanh::lean_ctor_set(v___x_2524_, 0, v___x_2526_);
                    v___x_2528_ = v___x_2524_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2529_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
                    v___x_2528_ = v_reuseFailAlloc_2529_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f___boxed(
    mut v_e_2534_: *mut leanh::LeanObject,
    mut v_a_2535_: *mut leanh::LeanObject,
    mut v_a_2536_: *mut leanh::LeanObject,
    mut v_a_2537_: *mut leanh::LeanObject,
    mut v_a_2538_: *mut leanh::LeanObject,
    mut v_a_2539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2540_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(
        v_e_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_,
    );
    leanh::lean_dec(v_a_2538_);
    leanh::lean_dec_ref(v_a_2537_);
    leanh::lean_dec(v_a_2536_);
    leanh::lean_dec_ref(v_a_2535_);
    return v_res_2540_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1_spec__3_spec__8(
    mut v_xs_2541_: *mut leanh::LeanObject,
    mut v_v_2542_: *mut leanh::LeanObject,
    mut v_i_2543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2544_ = lean_array_get_size(v_xs_2541_);
                v___x_2545_ = lean_nat_dec_lt(v_i_2543_, v___x_2544_);
                if v___x_2545_ == 0 {
                    leanh::lean_dec(v_i_2543_);
                    v___x_2546_ = leanh::lean_box(0);
                    return v___x_2546_;
                } else {
                    v___x_2547_ = lean_array_fget_borrowed(v_xs_2541_, v_i_2543_);
                    v___x_2548_ = lean_name_eq(v___x_2547_, v_v_2542_);
                    if v___x_2548_ == 0 {
                        v___x_2549_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2550_ = lean_nat_add(v_i_2543_, v___x_2549_);
                        leanh::lean_dec(v_i_2543_);
                        v_i_2543_ = v___x_2550_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2552_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2552_, 0, v_i_2543_);
                        return v___x_2552_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1_spec__3_spec__8___boxed(
    mut v_xs_2553_: *mut leanh::LeanObject,
    mut v_v_2554_: *mut leanh::LeanObject,
    mut v_i_2555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2556_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1_spec__3_spec__8(v_xs_2553_, v_v_2554_, v_i_2555_);
    leanh::lean_dec(v_v_2554_);
    leanh::lean_dec_ref(v_xs_2553_);
    return v_res_2556_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1_spec__3(
    mut v_xs_2557_: *mut leanh::LeanObject,
    mut v_v_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2559_ = leanh::lean_unsigned_to_nat(0);
    v___x_2560_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1_spec__3_spec__8(v_xs_2557_, v_v_2558_, v___x_2559_);
    return v___x_2560_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1_spec__3___boxed(
    mut v_xs_2561_: *mut leanh::LeanObject,
    mut v_v_2562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2563_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1_spec__3(v_xs_2561_, v_v_2562_);
    leanh::lean_dec(v_v_2562_);
    leanh::lean_dec_ref(v_xs_2561_);
    return v_res_2563_;
}
pub unsafe fn l_Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1(
    mut v_as_2564_: *mut leanh::LeanObject,
    mut v_a_2565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2566_ = l_Array_finIdxOf_x3f___at___00Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1_spec__3(v_as_2564_, v_a_2565_);
    if leanh::lean_obj_tag(v___x_2566_) == 0 {
        return v_as_2564_;
    } else {
        let mut v_val_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2567_ = leanh::lean_ctor_get(v___x_2566_, 0);
        leanh::lean_inc(v_val_2567_);
        leanh::lean_dec_ref_known(v___x_2566_, 1);
        v___x_2568_ = l_Array_eraseIdx___redArg(v_as_2564_, v_val_2567_);
        return v___x_2568_;
    }
}
pub unsafe fn l_Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1___boxed(
    mut v_as_2569_: *mut leanh::LeanObject,
    mut v_a_2570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2571_ = l_Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1(v_as_2569_, v_a_2570_);
    leanh::lean_dec(v_a_2570_);
    return v_res_2571_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__35_spec__36___redArg(
    mut v_x_2572_: *mut leanh::LeanObject,
    mut v_x_2573_: *mut leanh::LeanObject,
    mut v_x_2574_: *mut leanh::LeanObject,
    mut v_x_2575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: u8 = 0;
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: u8 = 0;
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2576_ = leanh::lean_ctor_get(v_x_2572_, 0);
                v_vs_2577_ = leanh::lean_ctor_get(v_x_2572_, 1);
                v_isSharedCheck_2601_ = (!leanh::lean_is_exclusive(v_x_2572_)) as u8;
                if v_isSharedCheck_2601_ == 0 {
                    v___x_2579_ = v_x_2572_;
                    v_isShared_2580_ = v_isSharedCheck_2601_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2577_);
                    leanh::lean_inc(v_ks_2576_);
                    leanh::lean_dec(v_x_2572_);
                    v___x_2579_ = leanh::lean_box(0);
                    v_isShared_2580_ = v_isSharedCheck_2601_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2581_ = lean_array_get_size(v_ks_2576_);
                v___x_2582_ = lean_nat_dec_lt(v_x_2573_, v___x_2581_);
                if v___x_2582_ == 0 {
                    leanh::lean_dec(v_x_2573_);
                    v___x_2583_ = lean_array_push(v_ks_2576_, v_x_2574_);
                    v___x_2584_ = lean_array_push(v_vs_2577_, v_x_2575_);
                    if v_isShared_2580_ == 0 {
                        leanh::lean_ctor_set(v___x_2579_, 1, v___x_2584_);
                        leanh::lean_ctor_set(v___x_2579_, 0, v___x_2583_);
                        v___x_2586_ = v___x_2579_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2587_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2583_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 1, v___x_2584_);
                        v___x_2586_ = v_reuseFailAlloc_2587_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2588_ = lean_array_fget_borrowed(v_ks_2576_, v_x_2573_);
                    v___x_2589_ = lean_name_eq(v_x_2574_, v_k_x27_2588_);
                    if v___x_2589_ == 0 {
                        if v_isShared_2580_ == 0 {
                            v___x_2591_ = v___x_2579_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2595_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_ks_2576_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_vs_2577_);
                            v___x_2591_ = v_reuseFailAlloc_2595_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2596_ = lean_array_fset(v_ks_2576_, v_x_2573_, v_x_2574_);
                        v___x_2597_ = lean_array_fset(v_vs_2577_, v_x_2573_, v_x_2575_);
                        leanh::lean_dec(v_x_2573_);
                        if v_isShared_2580_ == 0 {
                            leanh::lean_ctor_set(v___x_2579_, 1, v___x_2597_);
                            leanh::lean_ctor_set(v___x_2579_, 0, v___x_2596_);
                            v___x_2599_ = v___x_2579_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2600_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2596_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 1, v___x_2597_);
                            v___x_2599_ = v_reuseFailAlloc_2600_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2586_;
            }
            3 => {
                v___x_2592_ = leanh::lean_unsigned_to_nat(1);
                v___x_2593_ = lean_nat_add(v_x_2573_, v___x_2592_);
                leanh::lean_dec(v_x_2573_);
                v_x_2572_ = v___x_2591_;
                v_x_2573_ = v___x_2593_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__35___redArg(
    mut v_n_2602_: *mut leanh::LeanObject,
    mut v_k_2603_: *mut leanh::LeanObject,
    mut v_v_2604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2605_ = leanh::lean_unsigned_to_nat(0);
    v___x_2606_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__35_spec__36___redArg(v_n_2602_, v___x_2605_, v_k_2603_, v_v_2604_);
    return v___x_2606_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg___closed__0()
-> u64 {
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u64 = 0;
    v___x_2607_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2608_ = lean_uint64_of_nat(v___x_2607_);
    return v___x_2608_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__0()
-> usize {
    let mut v___x_2609_: usize = 0;
    let mut v___x_2610_: usize = 0;
    let mut v___x_2611_: usize = 0;
    v___x_2609_ = 5usize;
    v___x_2610_ = 1usize;
    v___x_2611_ = lean_usize_shift_left(v___x_2610_, v___x_2609_);
    return v___x_2611_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__1()
-> usize {
    let mut v___x_2612_: usize = 0;
    let mut v___x_2613_: usize = 0;
    let mut v___x_2614_: usize = 0;
    v___x_2612_ = 1usize;
    v___x_2613_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__0);
    v___x_2614_ = lean_usize_sub(v___x_2613_, v___x_2612_);
    return v___x_2614_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2615_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2615_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg(
    mut v_x_2616_: *mut leanh::LeanObject,
    mut v_x_2617_: usize,
    mut v_x_2618_: usize,
    mut v_x_2619_: *mut leanh::LeanObject,
    mut v_x_2620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: usize = 0;
    let mut v___x_2623_: usize = 0;
    let mut v___x_2624_: usize = 0;
    let mut v___x_2625_: usize = 0;
    let mut v_j_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2631_: u8 = 0;
    let mut v_v_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2645_: u8 = 0;
    let mut v___x_2646_: u8 = 0;
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v_node_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2656_: u8 = 0;
    let mut v___x_2657_: usize = 0;
    let mut v___x_2658_: usize = 0;
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2663_: u8 = 0;
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2665_: u8 = 0;
    let mut v_unused_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2676_: u8 = 0;
    let mut v_ks_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: usize = 0;
    let mut v___x_2683_: u8 = 0;
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: u8 = 0;
    let mut v_reuseFailAlloc_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2616_) == 0 {
                    v_es_2621_ = leanh::lean_ctor_get(v_x_2616_, 0);
                    v___x_2622_ = 5usize;
                    v___x_2623_ = 1usize;
                    v___x_2624_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__1);
                    v___x_2625_ = lean_usize_land(v_x_2617_, v___x_2624_);
                    v_j_2626_ = lean_usize_to_nat(v___x_2625_);
                    v___x_2627_ = lean_array_get_size(v_es_2621_);
                    v___x_2628_ = lean_nat_dec_lt(v_j_2626_, v___x_2627_);
                    if v___x_2628_ == 0 {
                        leanh::lean_dec(v_j_2626_);
                        leanh::lean_dec(v_x_2620_);
                        leanh::lean_dec(v_x_2619_);
                        return v_x_2616_;
                    } else {
                        leanh::lean_inc_ref(v_es_2621_);
                        v_isSharedCheck_2665_ = (!leanh::lean_is_exclusive(v_x_2616_)) as u8;
                        if v_isSharedCheck_2665_ == 0 {
                            v_unused_2666_ = leanh::lean_ctor_get(v_x_2616_, 0);
                            leanh::lean_dec(v_unused_2666_);
                            v___x_2630_ = v_x_2616_;
                            v_isShared_2631_ = v_isSharedCheck_2665_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2616_);
                            v___x_2630_ = leanh::lean_box(0);
                            v_isShared_2631_ = v_isSharedCheck_2665_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2667_ = leanh::lean_ctor_get(v_x_2616_, 0);
                    v_vs_2668_ = leanh::lean_ctor_get(v_x_2616_, 1);
                    v_isSharedCheck_2688_ = (!leanh::lean_is_exclusive(v_x_2616_)) as u8;
                    if v_isSharedCheck_2688_ == 0 {
                        v___x_2670_ = v_x_2616_;
                        v_isShared_2671_ = v_isSharedCheck_2688_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2668_);
                        leanh::lean_inc(v_ks_2667_);
                        leanh::lean_dec(v_x_2616_);
                        v___x_2670_ = leanh::lean_box(0);
                        v_isShared_2671_ = v_isSharedCheck_2688_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2632_ = lean_array_fget(v_es_2621_, v_j_2626_);
                v___x_2633_ = leanh::lean_box(0);
                v_xs_x27_2634_ = lean_array_fset(v_es_2621_, v_j_2626_, v___x_2633_);
                match leanh::lean_obj_tag(v_v_2632_) {
                    0 => {
                        v_key_2641_ = leanh::lean_ctor_get(v_v_2632_, 0);
                        v_val_2642_ = leanh::lean_ctor_get(v_v_2632_, 1);
                        v_isSharedCheck_2652_ = (!leanh::lean_is_exclusive(v_v_2632_)) as u8;
                        if v_isSharedCheck_2652_ == 0 {
                            v___x_2644_ = v_v_2632_;
                            v_isShared_2645_ = v_isSharedCheck_2652_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2642_);
                            leanh::lean_inc(v_key_2641_);
                            leanh::lean_dec(v_v_2632_);
                            v___x_2644_ = leanh::lean_box(0);
                            v_isShared_2645_ = v_isSharedCheck_2652_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2653_ = leanh::lean_ctor_get(v_v_2632_, 0);
                        v_isSharedCheck_2663_ = (!leanh::lean_is_exclusive(v_v_2632_)) as u8;
                        if v_isSharedCheck_2663_ == 0 {
                            v___x_2655_ = v_v_2632_;
                            v_isShared_2656_ = v_isSharedCheck_2663_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2653_);
                            leanh::lean_dec(v_v_2632_);
                            v___x_2655_ = leanh::lean_box(0);
                            v_isShared_2656_ = v_isSharedCheck_2663_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2664_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2664_, 0, v_x_2619_);
                        leanh::lean_ctor_set(v___x_2664_, 1, v_x_2620_);
                        v___y_2636_ = v___x_2664_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2637_ = lean_array_fset(v_xs_x27_2634_, v_j_2626_, v___y_2636_);
                leanh::lean_dec(v_j_2626_);
                if v_isShared_2631_ == 0 {
                    leanh::lean_ctor_set(v___x_2630_, 0, v___x_2637_);
                    v___x_2639_ = v___x_2630_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2640_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2637_);
                    v___x_2639_ = v_reuseFailAlloc_2640_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2639_;
            }
            4 => {
                v___x_2646_ = lean_name_eq(v_x_2619_, v_key_2641_);
                if v___x_2646_ == 0 {
                    leanh::lean_del_object(v___x_2644_);
                    v___x_2647_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2641_,
                        v_val_2642_,
                        v_x_2619_,
                        v_x_2620_,
                    );
                    v___x_2648_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2648_, 0, v___x_2647_);
                    v___y_2636_ = v___x_2648_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2642_);
                    leanh::lean_dec(v_key_2641_);
                    if v_isShared_2645_ == 0 {
                        leanh::lean_ctor_set(v___x_2644_, 1, v_x_2620_);
                        leanh::lean_ctor_set(v___x_2644_, 0, v_x_2619_);
                        v___x_2650_ = v___x_2644_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2651_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_x_2619_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_x_2620_);
                        v___x_2650_ = v_reuseFailAlloc_2651_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2636_ = v___x_2650_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2657_ = lean_usize_shift_right(v_x_2617_, v___x_2622_);
                v___x_2658_ = lean_usize_add(v_x_2618_, v___x_2623_);
                v___x_2659_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg(v_node_2653_, v___x_2657_, v___x_2658_, v_x_2619_, v_x_2620_);
                if v_isShared_2656_ == 0 {
                    leanh::lean_ctor_set(v___x_2655_, 0, v___x_2659_);
                    v___x_2661_ = v___x_2655_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2662_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
                    v___x_2661_ = v_reuseFailAlloc_2662_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2636_ = v___x_2661_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2671_ == 0 {
                    v___x_2673_ = v___x_2670_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2687_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_ks_2667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_vs_2668_);
                    v___x_2673_ = v_reuseFailAlloc_2687_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2674_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__35___redArg(v___x_2673_, v_x_2619_, v_x_2620_);
                v___x_2682_ = 7usize;
                v___x_2683_ = lean_usize_dec_le(v___x_2682_, v_x_2618_);
                if v___x_2683_ == 0 {
                    v___x_2684_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2674_);
                    v___x_2685_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2686_ = lean_nat_dec_lt(v___x_2684_, v___x_2685_);
                    leanh::lean_dec(v___x_2684_);
                    v___y_2676_ = v___x_2686_;
                    state = 10;
                    continue;
                } else {
                    v___y_2676_ = v___x_2683_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2676_ == 0 {
                    v_ks_2677_ = leanh::lean_ctor_get(v_newNode_2674_, 0);
                    leanh::lean_inc_ref(v_ks_2677_);
                    v_vs_2678_ = leanh::lean_ctor_get(v_newNode_2674_, 1);
                    leanh::lean_inc_ref(v_vs_2678_);
                    leanh::lean_dec_ref(v_newNode_2674_);
                    v___x_2679_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2680_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___closed__2);
                    v___x_2681_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg(v_x_2618_, v_ks_2677_, v_vs_2678_, v___x_2679_, v___x_2680_);
                    leanh::lean_dec_ref(v_vs_2678_);
                    leanh::lean_dec_ref(v_ks_2677_);
                    return v___x_2681_;
                } else {
                    return v_newNode_2674_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg(
    mut v_depth_2689_: usize,
    mut v_keys_2690_: *mut leanh::LeanObject,
    mut v_vals_2691_: *mut leanh::LeanObject,
    mut v_i_2692_: *mut leanh::LeanObject,
    mut v_entries_2693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: u8 = 0;
    let mut v_k_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2699_: u64 = 0;
    let mut v_h_2700_: usize = 0;
    let mut v___x_2701_: usize = 0;
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: usize = 0;
    let mut v___x_2704_: usize = 0;
    let mut v___x_2705_: usize = 0;
    let mut v_h_2706_: usize = 0;
    let mut v___x_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: u64 = 0;
    let mut v_hash_2711_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2694_ = lean_array_get_size(v_keys_2690_);
                v___x_2695_ = lean_nat_dec_lt(v_i_2692_, v___x_2694_);
                if v___x_2695_ == 0 {
                    leanh::lean_dec(v_i_2692_);
                    return v_entries_2693_;
                } else {
                    v_k_2696_ = lean_array_fget_borrowed(v_keys_2690_, v_i_2692_);
                    v_v_2697_ = lean_array_fget_borrowed(v_vals_2691_, v_i_2692_);
                    if leanh::lean_obj_tag(v_k_2696_) == 0 {
                        v___x_2710_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg___closed__0);
                        v___y_2699_ = v___x_2710_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2711_ = leanh::lean_ctor_get_uint64(
                            v_k_2696_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2699_ = v_hash_2711_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2700_ = lean_uint64_to_usize(v___y_2699_);
                v___x_2701_ = 5usize;
                v___x_2702_ = leanh::lean_unsigned_to_nat(1);
                v___x_2703_ = 1usize;
                v___x_2704_ = lean_usize_sub(v_depth_2689_, v___x_2703_);
                v___x_2705_ = lean_usize_mul(v___x_2701_, v___x_2704_);
                v_h_2706_ = lean_usize_shift_right(v_h_2700_, v___x_2705_);
                v___x_2707_ = lean_nat_add(v_i_2692_, v___x_2702_);
                leanh::lean_dec(v_i_2692_);
                leanh::lean_inc(v_v_2697_);
                leanh::lean_inc(v_k_2696_);
                v___x_2708_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg(v_entries_2693_, v_h_2706_, v_depth_2689_, v_k_2696_, v_v_2697_);
                v_i_2692_ = v___x_2707_;
                v_entries_2693_ = v___x_2708_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg___boxed(
    mut v_depth_2712_: *mut leanh::LeanObject,
    mut v_keys_2713_: *mut leanh::LeanObject,
    mut v_vals_2714_: *mut leanh::LeanObject,
    mut v_i_2715_: *mut leanh::LeanObject,
    mut v_entries_2716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2717_: usize = 0;
    let mut v_res_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2717_ = leanh::lean_unbox_usize(v_depth_2712_);
    leanh::lean_dec(v_depth_2712_);
    v_res_2718_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg(v_depth_boxed_2717_, v_keys_2713_, v_vals_2714_, v_i_2715_, v_entries_2716_);
    leanh::lean_dec_ref(v_vals_2714_);
    leanh::lean_dec_ref(v_keys_2713_);
    return v_res_2718_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg___boxed(
    mut v_x_2719_: *mut leanh::LeanObject,
    mut v_x_2720_: *mut leanh::LeanObject,
    mut v_x_2721_: *mut leanh::LeanObject,
    mut v_x_2722_: *mut leanh::LeanObject,
    mut v_x_2723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_15186__boxed_2724_: usize = 0;
    let mut v_x_15187__boxed_2725_: usize = 0;
    let mut v_res_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_15186__boxed_2724_ = leanh::lean_unbox_usize(v_x_2720_);
    leanh::lean_dec(v_x_2720_);
    v_x_15187__boxed_2725_ = leanh::lean_unbox_usize(v_x_2721_);
    leanh::lean_dec(v_x_2721_);
    v_res_2726_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg(v_x_2719_, v_x_15186__boxed_2724_, v_x_15187__boxed_2725_, v_x_2722_, v_x_2723_);
    return v_res_2726_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20___redArg(
    mut v_x_2727_: *mut leanh::LeanObject,
    mut v_x_2728_: *mut leanh::LeanObject,
    mut v_x_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2731_: u64 = 0;
    let mut v___x_2732_: usize = 0;
    let mut v___x_2733_: usize = 0;
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: u64 = 0;
    let mut v_hash_2736_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2728_) == 0 {
                    v___x_2735_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg___closed__0);
                    v___y_2731_ = v___x_2735_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2736_ = leanh::lean_ctor_get_uint64(
                        v_x_2728_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2731_ = v_hash_2736_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2732_ = lean_uint64_to_usize(v___y_2731_);
                v___x_2733_ = 1usize;
                v___x_2734_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg(v_x_2727_, v___x_2732_, v___x_2733_, v_x_2728_, v_x_2729_);
                return v___x_2734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___lam__0(
    mut v_structName_2737_: *mut leanh::LeanObject,
    mut v_resolutionOrder_2738_: *mut leanh::LeanObject,
    mut v_s_2739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2740_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20___redArg(v_s_2739_, v_structName_2737_, v_resolutionOrder_2738_);
    return v___x_2740_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2741_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2741_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2742_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__0_once), _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__0);
    v___x_2743_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2743_, 0, v___x_2742_);
    return v___x_2743_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2744_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__1_once), _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__1);
    v___x_2745_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2745_, 0, v___x_2744_);
    leanh::lean_ctor_set(v___x_2745_, 1, v___x_2744_);
    return v___x_2745_;
}
pub unsafe fn _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2746_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__1_once), _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__1);
    v___x_2747_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_2747_, 0, v___x_2746_);
    leanh::lean_ctor_set(v___x_2747_, 1, v___x_2746_);
    leanh::lean_ctor_set(v___x_2747_, 2, v___x_2746_);
    leanh::lean_ctor_set(v___x_2747_, 3, v___x_2746_);
    leanh::lean_ctor_set(v___x_2747_, 4, v___x_2746_);
    leanh::lean_ctor_set(v___x_2747_, 5, v___x_2746_);
    return v___x_2747_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_structName_2748_: *mut leanh::LeanObject,
    mut v_resolutionOrder_2749_: *mut leanh::LeanObject,
    mut v___y_2750_: *mut leanh::LeanObject,
    mut v___y_2751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2764_: u8 = 0;
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2781_: u8 = 0;
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2789_: u8 = 0;
    let mut v_unused_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2792_: u8 = 0;
    let mut v_unused_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2753_ = lean_st_ref_take(v___y_2751_);
                v_env_2754_ = leanh::lean_ctor_get(v___x_2753_, 0);
                v_nextMacroScope_2755_ = leanh::lean_ctor_get(v___x_2753_, 1);
                v_ngen_2756_ = leanh::lean_ctor_get(v___x_2753_, 2);
                v_auxDeclNGen_2757_ = leanh::lean_ctor_get(v___x_2753_, 3);
                v_traceState_2758_ = leanh::lean_ctor_get(v___x_2753_, 4);
                v_messages_2759_ = leanh::lean_ctor_get(v___x_2753_, 6);
                v_infoState_2760_ = leanh::lean_ctor_get(v___x_2753_, 7);
                v_snapshotTasks_2761_ = leanh::lean_ctor_get(v___x_2753_, 8);
                v_isSharedCheck_2792_ = (!leanh::lean_is_exclusive(v___x_2753_)) as u8;
                if v_isSharedCheck_2792_ == 0 {
                    v_unused_2793_ = leanh::lean_ctor_get(v___x_2753_, 5);
                    leanh::lean_dec(v_unused_2793_);
                    v___x_2763_ = v___x_2753_;
                    v_isShared_2764_ = v_isSharedCheck_2792_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2761_);
                    leanh::lean_inc(v_infoState_2760_);
                    leanh::lean_inc(v_messages_2759_);
                    leanh::lean_inc(v_traceState_2758_);
                    leanh::lean_inc(v_auxDeclNGen_2757_);
                    leanh::lean_inc(v_ngen_2756_);
                    leanh::lean_inc(v_nextMacroScope_2755_);
                    leanh::lean_inc(v_env_2754_);
                    leanh::lean_dec(v___x_2753_);
                    v___x_2763_ = leanh::lean_box(0);
                    v_isShared_2764_ = v_isSharedCheck_2792_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2765_ = l_Lean_structureResolutionExt;
                v_asyncMode_2766_ = leanh::lean_ctor_get(v___x_2765_, 2);
                v___f_2767_ = leanh::lean_alloc_closure(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_2767_, 0, v_structName_2748_);
                leanh::lean_closure_set(v___f_2767_, 1, v_resolutionOrder_2749_);
                v___x_2768_ = leanh::lean_box(0);
                v___x_2769_ = l_Lean_EnvExtension_modifyState___redArg(
                    v___x_2765_,
                    v_env_2754_,
                    v___f_2767_,
                    v_asyncMode_2766_,
                    v___x_2768_,
                );
                v___x_2770_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__2_once), _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__2);
                if v_isShared_2764_ == 0 {
                    leanh::lean_ctor_set(v___x_2763_, 5, v___x_2770_);
                    leanh::lean_ctor_set(v___x_2763_, 0, v___x_2769_);
                    v___x_2772_ = v___x_2763_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2791_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 1, v_nextMacroScope_2755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 2, v_ngen_2756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 3, v_auxDeclNGen_2757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 4, v_traceState_2758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 5, v___x_2770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 6, v_messages_2759_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 7, v_infoState_2760_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2791_, 8, v_snapshotTasks_2761_);
                    v___x_2772_ = v_reuseFailAlloc_2791_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2773_ = lean_st_ref_set(v___y_2751_, v___x_2772_);
                v___x_2774_ = lean_st_ref_take(v___y_2750_);
                v_mctx_2775_ = leanh::lean_ctor_get(v___x_2774_, 0);
                v_zetaDeltaFVarIds_2776_ = leanh::lean_ctor_get(v___x_2774_, 2);
                v_postponed_2777_ = leanh::lean_ctor_get(v___x_2774_, 3);
                v_diag_2778_ = leanh::lean_ctor_get(v___x_2774_, 4);
                v_isSharedCheck_2789_ = (!leanh::lean_is_exclusive(v___x_2774_)) as u8;
                if v_isSharedCheck_2789_ == 0 {
                    v_unused_2790_ = leanh::lean_ctor_get(v___x_2774_, 1);
                    leanh::lean_dec(v_unused_2790_);
                    v___x_2780_ = v___x_2774_;
                    v_isShared_2781_ = v_isSharedCheck_2789_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2778_);
                    leanh::lean_inc(v_postponed_2777_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2776_);
                    leanh::lean_inc(v_mctx_2775_);
                    leanh::lean_dec(v___x_2774_);
                    v___x_2780_ = leanh::lean_box(0);
                    v_isShared_2781_ = v_isSharedCheck_2789_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2782_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once), _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___closed__3);
                if v_isShared_2781_ == 0 {
                    leanh::lean_ctor_set(v___x_2780_, 1, v___x_2782_);
                    v___x_2784_ = v___x_2780_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2788_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_mctx_2775_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 1, v___x_2782_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2788_,
                        2,
                        v_zetaDeltaFVarIds_2776_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 3, v_postponed_2777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2788_, 4, v_diag_2778_);
                    v___x_2784_ = v_reuseFailAlloc_2788_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2785_ = lean_st_ref_set(v___y_2750_, v___x_2784_);
                v___x_2786_ = leanh::lean_box(0);
                v___x_2787_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2787_, 0, v___x_2786_);
                return v___x_2787_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_structName_2794_: *mut leanh::LeanObject,
    mut v_resolutionOrder_2795_: *mut leanh::LeanObject,
    mut v___y_2796_: *mut leanh::LeanObject,
    mut v___y_2797_: *mut leanh::LeanObject,
    mut v___y_2798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2799_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg(v_structName_2794_, v_resolutionOrder_2795_, v___y_2796_, v___y_2797_);
    leanh::lean_dec(v___y_2797_);
    leanh::lean_dec(v___y_2796_);
    return v_res_2799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__3(
    mut v_sz_2800_: usize,
    mut v_i_2801_: usize,
    mut v_bs_2802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2803_: u8 = 0;
    let mut v_v_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_structName_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: usize = 0;
    let mut v___x_2809_: usize = 0;
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2803_ = lean_usize_dec_lt(v_i_2801_, v_sz_2800_);
                if v___x_2803_ == 0 {
                    return v_bs_2802_;
                } else {
                    v_v_2804_ = lean_array_uget_borrowed(v_bs_2802_, v_i_2801_);
                    v_structName_2805_ = leanh::lean_ctor_get(v_v_2804_, 0);
                    leanh::lean_inc(v_structName_2805_);
                    v___x_2806_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2807_ = lean_array_uset(v_bs_2802_, v_i_2801_, v___x_2806_);
                    v___x_2808_ = 1usize;
                    v___x_2809_ = lean_usize_add(v_i_2801_, v___x_2808_);
                    v___x_2810_ = lean_array_uset(v_bs_x27_2807_, v_i_2801_, v_structName_2805_);
                    v_i_2801_ = v___x_2809_;
                    v_bs_2802_ = v___x_2810_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_sz_2812_: *mut leanh::LeanObject,
    mut v_i_2813_: *mut leanh::LeanObject,
    mut v_bs_2814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2815_: usize = 0;
    let mut v_i_boxed_2816_: usize = 0;
    let mut v_res_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2815_ = leanh::lean_unbox_usize(v_sz_2812_);
    leanh::lean_dec(v_sz_2812_);
    v_i_boxed_2816_ = leanh::lean_unbox_usize(v_i_2813_);
    leanh::lean_dec(v_i_2813_);
    v_res_2817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__3(v_sz_boxed_2815_, v_i_boxed_2816_, v_bs_2814_);
    return v_res_2817_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16_spec__25___redArg(
    mut v_hi_2818_: *mut leanh::LeanObject,
    mut v_pivot_2819_: *mut leanh::LeanObject,
    mut v_as_2820_: *mut leanh::LeanObject,
    mut v_i_2821_: *mut leanh::LeanObject,
    mut v_k_2822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2823_: u8 = 0;
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: u8 = 0;
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2823_ = lean_nat_dec_lt(v_k_2822_, v_hi_2818_);
                if v___x_2823_ == 0 {
                    leanh::lean_dec(v_k_2822_);
                    v___x_2824_ = lean_array_fswap(v_as_2820_, v_i_2821_, v_hi_2818_);
                    v___x_2825_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2825_, 0, v_i_2821_);
                    leanh::lean_ctor_set(v___x_2825_, 1, v___x_2824_);
                    return v___x_2825_;
                } else {
                    v___x_2826_ = lean_array_fget_borrowed(v_as_2820_, v_k_2822_);
                    v___x_2827_ = l_Lean_Name_lt(v___x_2826_, v_pivot_2819_);
                    if v___x_2827_ == 0 {
                        v___x_2828_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2829_ = lean_nat_add(v_k_2822_, v___x_2828_);
                        leanh::lean_dec(v_k_2822_);
                        v_k_2822_ = v___x_2829_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2831_ = lean_array_fswap(v_as_2820_, v_i_2821_, v_k_2822_);
                        v___x_2832_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2833_ = lean_nat_add(v_i_2821_, v___x_2832_);
                        leanh::lean_dec(v_i_2821_);
                        v___x_2834_ = lean_nat_add(v_k_2822_, v___x_2832_);
                        leanh::lean_dec(v_k_2822_);
                        v_as_2820_ = v___x_2831_;
                        v_i_2821_ = v___x_2833_;
                        v_k_2822_ = v___x_2834_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16_spec__25___redArg___boxed(
    mut v_hi_2836_: *mut leanh::LeanObject,
    mut v_pivot_2837_: *mut leanh::LeanObject,
    mut v_as_2838_: *mut leanh::LeanObject,
    mut v_i_2839_: *mut leanh::LeanObject,
    mut v_k_2840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2841_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16_spec__25___redArg(v_hi_2836_, v_pivot_2837_, v_as_2838_, v_i_2839_, v_k_2840_);
    leanh::lean_dec(v_pivot_2837_);
    leanh::lean_dec(v_hi_2836_);
    return v_res_2841_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16___redArg(
    mut v_n_2842_: *mut leanh::LeanObject,
    mut v_as_2843_: *mut leanh::LeanObject,
    mut v_lo_2844_: *mut leanh::LeanObject,
    mut v_hi_2845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: u8 = 0;
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: u8 = 0;
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: u8 = 0;
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: u8 = 0;
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2857_ = lean_nat_dec_lt(v_lo_2844_, v_hi_2845_);
                if v___x_2857_ == 0 {
                    leanh::lean_dec(v_lo_2844_);
                    return v_as_2843_;
                } else {
                    v___x_2858_ = lean_nat_add(v_lo_2844_, v_hi_2845_);
                    v___x_2859_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_2860_ = lean_nat_shiftr(v___x_2858_, v___x_2859_);
                    leanh::lean_dec(v___x_2858_);
                    v___x_2873_ = lean_array_fget_borrowed(v_as_2843_, v_mid_2860_);
                    v___x_2874_ = lean_array_fget_borrowed(v_as_2843_, v_lo_2844_);
                    v___x_2875_ = l_Lean_Name_lt(v___x_2873_, v___x_2874_);
                    if v___x_2875_ == 0 {
                        v___y_2868_ = v_as_2843_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2876_ = lean_array_fswap(v_as_2843_, v_lo_2844_, v_mid_2860_);
                        v___y_2868_ = v___x_2876_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2848_ = lean_array_fget(v___y_2847_, v_hi_2845_);
                leanh::lean_inc_n(v_lo_2844_, 2);
                v___x_2849_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16_spec__25___redArg(v_hi_2845_, v_pivot_2848_, v___y_2847_, v_lo_2844_, v_lo_2844_);
                leanh::lean_dec(v_pivot_2848_);
                v_fst_2850_ = leanh::lean_ctor_get(v___x_2849_, 0);
                leanh::lean_inc(v_fst_2850_);
                v_snd_2851_ = leanh::lean_ctor_get(v___x_2849_, 1);
                leanh::lean_inc(v_snd_2851_);
                leanh::lean_dec_ref(v___x_2849_);
                v___x_2852_ = lean_nat_dec_le(v_hi_2845_, v_fst_2850_);
                if v___x_2852_ == 0 {
                    v___x_2853_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16___redArg(v_n_2842_, v_snd_2851_, v_lo_2844_, v_fst_2850_);
                    v___x_2854_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2855_ = lean_nat_add(v_fst_2850_, v___x_2854_);
                    leanh::lean_dec(v_fst_2850_);
                    v_as_2843_ = v___x_2853_;
                    v_lo_2844_ = v___x_2855_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2850_);
                    leanh::lean_dec(v_lo_2844_);
                    return v_snd_2851_;
                }
            }
            2 => {
                v___x_2863_ = lean_array_fget_borrowed(v___y_2862_, v_mid_2860_);
                v___x_2864_ = lean_array_fget_borrowed(v___y_2862_, v_hi_2845_);
                v___x_2865_ = l_Lean_Name_lt(v___x_2863_, v___x_2864_);
                if v___x_2865_ == 0 {
                    leanh::lean_dec(v_mid_2860_);
                    v___y_2847_ = v___y_2862_;
                    state = 1;
                    continue;
                } else {
                    v___x_2866_ = lean_array_fswap(v___y_2862_, v_mid_2860_, v_hi_2845_);
                    leanh::lean_dec(v_mid_2860_);
                    v___y_2847_ = v___x_2866_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2869_ = lean_array_fget_borrowed(v___y_2868_, v_hi_2845_);
                v___x_2870_ = lean_array_fget_borrowed(v___y_2868_, v_lo_2844_);
                v___x_2871_ = l_Lean_Name_lt(v___x_2869_, v___x_2870_);
                if v___x_2871_ == 0 {
                    v___y_2862_ = v___y_2868_;
                    state = 2;
                    continue;
                } else {
                    v___x_2872_ = lean_array_fswap(v___y_2868_, v_lo_2844_, v_hi_2845_);
                    v___y_2862_ = v___x_2872_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16___redArg___boxed(
    mut v_n_2877_: *mut leanh::LeanObject,
    mut v_as_2878_: *mut leanh::LeanObject,
    mut v_lo_2879_: *mut leanh::LeanObject,
    mut v_hi_2880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2881_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16___redArg(v_n_2877_, v_as_2878_, v_lo_2879_, v_hi_2880_);
    leanh::lean_dec(v_hi_2880_);
    leanh::lean_dec(v_n_2877_);
    return v_res_2881_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__8(
    mut v_snd_2882_: *mut leanh::LeanObject,
    mut v_as_2883_: *mut leanh::LeanObject,
    mut v_i_2884_: usize,
    mut v_stop_2885_: usize,
) -> u8 {
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2889_: usize = 0;
    let mut v___x_2890_: usize = 0;
    let mut v___x_2892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2886_ = lean_usize_dec_eq(v_i_2884_, v_stop_2885_);
                if v___x_2886_ == 0 {
                    v___x_2887_ = lean_array_uget_borrowed(v_as_2883_, v_i_2884_);
                    v___x_2888_ = lean_name_eq(v___x_2887_, v_snd_2882_);
                    if v___x_2888_ == 0 {
                        v___x_2889_ = 1usize;
                        v___x_2890_ = lean_usize_add(v_i_2884_, v___x_2889_);
                        v_i_2884_ = v___x_2890_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2888_;
                    }
                } else {
                    v___x_2892_ = 0;
                    return v___x_2892_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__8___boxed(
    mut v_snd_2893_: *mut leanh::LeanObject,
    mut v_as_2894_: *mut leanh::LeanObject,
    mut v_i_2895_: *mut leanh::LeanObject,
    mut v_stop_2896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2897_: usize = 0;
    let mut v_stop_boxed_2898_: usize = 0;
    let mut v_res_2899_: u8 = 0;
    let mut v_r_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2897_ = leanh::lean_unbox_usize(v_i_2895_);
    leanh::lean_dec(v_i_2895_);
    v_stop_boxed_2898_ = leanh::lean_unbox_usize(v_stop_2896_);
    leanh::lean_dec(v_stop_2896_);
    v_res_2899_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__8(v_snd_2893_, v_as_2894_, v_i_boxed_2897_, v_stop_boxed_2898_);
    leanh::lean_dec_ref(v_as_2894_);
    leanh::lean_dec(v_snd_2893_);
    v_r_2900_ = leanh::lean_box((v_res_2899_) as usize);
    return v_r_2900_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__17(
    mut v_snd_2901_: *mut leanh::LeanObject,
    mut v_as_2902_: *mut leanh::LeanObject,
    mut v_i_2903_: usize,
    mut v_stop_2904_: usize,
    mut v_b_2905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: usize = 0;
    let mut v___x_2909_: usize = 0;
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    let mut v___x_2922_: usize = 0;
    let mut v___x_2923_: usize = 0;
    let mut v___x_2924_: u8 = 0;
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: u8 = 0;
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2911_ = lean_usize_dec_eq(v_i_2903_, v_stop_2904_);
                if v___x_2911_ == 0 {
                    v___x_2912_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2913_ = lean_array_uget_borrowed(v_as_2902_, v_i_2903_);
                    v___x_2914_ = lean_array_get_size(v___x_2913_);
                    leanh::lean_inc(v___x_2913_);
                    v___x_2915_ =
                        l_Array_toSubarray___redArg(v___x_2913_, v___x_2912_, v___x_2914_);
                    v_array_2916_ = leanh::lean_ctor_get(v___x_2915_, 0);
                    leanh::lean_inc_ref(v_array_2916_);
                    v_start_2917_ = leanh::lean_ctor_get(v___x_2915_, 1);
                    leanh::lean_inc(v_start_2917_);
                    v_stop_2918_ = leanh::lean_ctor_get(v___x_2915_, 2);
                    leanh::lean_inc(v_stop_2918_);
                    leanh::lean_dec_ref(v___x_2915_);
                    v___x_2926_ = lean_nat_dec_lt(v_start_2917_, v_stop_2918_);
                    if v___x_2926_ == 0 {
                        leanh::lean_dec(v_stop_2918_);
                        leanh::lean_dec(v_start_2917_);
                        leanh::lean_dec_ref(v_array_2916_);
                        v___y_2907_ = v_b_2905_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2927_ = lean_array_get_size(v_array_2916_);
                        v___x_2928_ = lean_nat_dec_le(v_stop_2918_, v___x_2927_);
                        if v___x_2928_ == 0 {
                            leanh::lean_dec(v_stop_2918_);
                            v___y_2920_ = v___x_2927_;
                            state = 2;
                            continue;
                        } else {
                            v___y_2920_ = v_stop_2918_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    return v_b_2905_;
                }
            }
            1 => {
                v___x_2908_ = 1usize;
                v___x_2909_ = lean_usize_add(v_i_2903_, v___x_2908_);
                v_i_2903_ = v___x_2909_;
                v_b_2905_ = v___y_2907_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2921_ = lean_nat_dec_lt(v_start_2917_, v___y_2920_);
                if v___x_2921_ == 0 {
                    leanh::lean_dec(v___y_2920_);
                    leanh::lean_dec(v_start_2917_);
                    leanh::lean_dec_ref(v_array_2916_);
                    v___y_2907_ = v_b_2905_;
                    state = 1;
                    continue;
                } else {
                    v___x_2922_ = lean_usize_of_nat(v_start_2917_);
                    leanh::lean_dec(v_start_2917_);
                    v___x_2923_ = lean_usize_of_nat(v___y_2920_);
                    leanh::lean_dec(v___y_2920_);
                    v___x_2924_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__8(v_snd_2901_, v_array_2916_, v___x_2922_, v___x_2923_);
                    leanh::lean_dec_ref(v_array_2916_);
                    if v___x_2924_ == 0 {
                        v___y_2907_ = v_b_2905_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_2913_);
                        v___x_2925_ = lean_array_push(v_b_2905_, v___x_2913_);
                        v___y_2907_ = v___x_2925_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__17___boxed(
    mut v_snd_2929_: *mut leanh::LeanObject,
    mut v_as_2930_: *mut leanh::LeanObject,
    mut v_i_2931_: *mut leanh::LeanObject,
    mut v_stop_2932_: *mut leanh::LeanObject,
    mut v_b_2933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2934_: usize = 0;
    let mut v_stop_boxed_2935_: usize = 0;
    let mut v_res_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2934_ = leanh::lean_unbox_usize(v_i_2931_);
    leanh::lean_dec(v_i_2931_);
    v_stop_boxed_2935_ = leanh::lean_unbox_usize(v_stop_2932_);
    leanh::lean_dec(v_stop_2932_);
    v_res_2936_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__17(v_snd_2929_, v_as_2930_, v_i_boxed_2934_, v_stop_boxed_2935_, v_b_2933_);
    leanh::lean_dec_ref(v_as_2930_);
    leanh::lean_dec(v_snd_2929_);
    return v_res_2936_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__9(
    mut v_snd_2937_: *mut leanh::LeanObject,
    mut v_as_2938_: *mut leanh::LeanObject,
    mut v_i_2939_: usize,
    mut v_stop_2940_: usize,
    mut v_b_2941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: usize = 0;
    let mut v___x_2945_: usize = 0;
    let mut v___x_2947_: u8 = 0;
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: u8 = 0;
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2947_ = lean_usize_dec_eq(v_i_2939_, v_stop_2940_);
                if v___x_2947_ == 0 {
                    v___x_2948_ = lean_array_uget_borrowed(v_as_2938_, v_i_2939_);
                    v___x_2949_ = lean_name_eq(v___x_2948_, v_snd_2937_);
                    if v___x_2949_ == 0 {
                        leanh::lean_inc(v___x_2948_);
                        v___x_2950_ = lean_array_push(v_b_2941_, v___x_2948_);
                        v___y_2943_ = v___x_2950_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2943_ = v_b_2941_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2941_;
                }
            }
            1 => {
                v___x_2944_ = 1usize;
                v___x_2945_ = lean_usize_add(v_i_2939_, v___x_2944_);
                v_i_2939_ = v___x_2945_;
                v_b_2941_ = v___y_2943_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__9___boxed(
    mut v_snd_2951_: *mut leanh::LeanObject,
    mut v_as_2952_: *mut leanh::LeanObject,
    mut v_i_2953_: *mut leanh::LeanObject,
    mut v_stop_2954_: *mut leanh::LeanObject,
    mut v_b_2955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2956_: usize = 0;
    let mut v_stop_boxed_2957_: usize = 0;
    let mut v_res_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2956_ = leanh::lean_unbox_usize(v_i_2953_);
    leanh::lean_dec(v_i_2953_);
    v_stop_boxed_2957_ = leanh::lean_unbox_usize(v_stop_2954_);
    leanh::lean_dec(v_stop_2954_);
    v_res_2958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__9(v_snd_2951_, v_as_2952_, v_i_boxed_2956_, v_stop_boxed_2957_, v_b_2955_);
    leanh::lean_dec_ref(v_as_2952_);
    leanh::lean_dec(v_snd_2951_);
    return v_res_2958_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10(
    mut v_snd_2961_: *mut leanh::LeanObject,
    mut v_sz_2962_: usize,
    mut v_i_2963_: usize,
    mut v_bs_2964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2965_: u8 = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: usize = 0;
    let mut v___x_2972_: usize = 0;
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: u8 = 0;
    let mut v___x_2978_: u8 = 0;
    let mut v___x_2979_: usize = 0;
    let mut v___x_2980_: usize = 0;
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: usize = 0;
    let mut v___x_2983_: usize = 0;
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2965_ = lean_usize_dec_lt(v_i_2963_, v_sz_2962_);
                if v___x_2965_ == 0 {
                    return v_bs_2964_;
                } else {
                    v___x_2966_ = leanh::lean_unsigned_to_nat(0);
                    v_v_2967_ = lean_array_uget(v_bs_2964_, v_i_2963_);
                    v_bs_x27_2968_ = lean_array_uset(v_bs_2964_, v_i_2963_, v___x_2966_);
                    v___x_2975_ = lean_array_get_size(v_v_2967_);
                    v___x_2976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10___closed__0;
                    v___x_2977_ = lean_nat_dec_lt(v___x_2966_, v___x_2975_);
                    if v___x_2977_ == 0 {
                        leanh::lean_dec(v_v_2967_);
                        v___y_2970_ = v___x_2976_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2978_ = lean_nat_dec_le(v___x_2975_, v___x_2975_);
                        if v___x_2978_ == 0 {
                            if v___x_2977_ == 0 {
                                leanh::lean_dec(v_v_2967_);
                                v___y_2970_ = v___x_2976_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2979_ = 0usize;
                                v___x_2980_ = lean_usize_of_nat(v___x_2975_);
                                v___x_2981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__9(v_snd_2961_, v_v_2967_, v___x_2979_, v___x_2980_, v___x_2976_);
                                leanh::lean_dec(v_v_2967_);
                                v___y_2970_ = v___x_2981_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2982_ = 0usize;
                            v___x_2983_ = lean_usize_of_nat(v___x_2975_);
                            v___x_2984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__9(v_snd_2961_, v_v_2967_, v___x_2982_, v___x_2983_, v___x_2976_);
                            leanh::lean_dec(v_v_2967_);
                            v___y_2970_ = v___x_2984_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2971_ = 1usize;
                v___x_2972_ = lean_usize_add(v_i_2963_, v___x_2971_);
                v___x_2973_ = lean_array_uset(v_bs_x27_2968_, v_i_2963_, v___y_2970_);
                v_i_2963_ = v___x_2972_;
                v_bs_2964_ = v___x_2973_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10___boxed(
    mut v_snd_2985_: *mut leanh::LeanObject,
    mut v_sz_2986_: *mut leanh::LeanObject,
    mut v_i_2987_: *mut leanh::LeanObject,
    mut v_bs_2988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2989_: usize = 0;
    let mut v_i_boxed_2990_: usize = 0;
    let mut v_res_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2989_ = leanh::lean_unbox_usize(v_sz_2986_);
    leanh::lean_dec(v_sz_2986_);
    v_i_boxed_2990_ = leanh::lean_unbox_usize(v_i_2987_);
    leanh::lean_dec(v_i_2987_);
    v_res_2991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10(v_snd_2985_, v_sz_boxed_2989_, v_i_boxed_2990_, v_bs_2988_);
    leanh::lean_dec(v_snd_2985_);
    return v_res_2991_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__12_spec__19(
    mut v_a_2992_: *mut leanh::LeanObject,
    mut v_as_2993_: *mut leanh::LeanObject,
    mut v_i_2994_: usize,
    mut v_stop_2995_: usize,
) -> u8 {
    let mut v___x_2996_: u8 = 0;
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: usize = 0;
    let mut v___x_3000_: usize = 0;
    let mut v___x_3002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2996_ = lean_usize_dec_eq(v_i_2994_, v_stop_2995_);
                if v___x_2996_ == 0 {
                    v___x_2997_ = lean_array_uget_borrowed(v_as_2993_, v_i_2994_);
                    v___x_2998_ = lean_name_eq(v_a_2992_, v___x_2997_);
                    if v___x_2998_ == 0 {
                        v___x_2999_ = 1usize;
                        v___x_3000_ = lean_usize_add(v_i_2994_, v___x_2999_);
                        v_i_2994_ = v___x_3000_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2998_;
                    }
                } else {
                    v___x_3002_ = 0;
                    return v___x_3002_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__12_spec__19___boxed(
    mut v_a_3003_: *mut leanh::LeanObject,
    mut v_as_3004_: *mut leanh::LeanObject,
    mut v_i_3005_: *mut leanh::LeanObject,
    mut v_stop_3006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3007_: usize = 0;
    let mut v_stop_boxed_3008_: usize = 0;
    let mut v_res_3009_: u8 = 0;
    let mut v_r_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3007_ = leanh::lean_unbox_usize(v_i_3005_);
    leanh::lean_dec(v_i_3005_);
    v_stop_boxed_3008_ = leanh::lean_unbox_usize(v_stop_3006_);
    leanh::lean_dec(v_stop_3006_);
    v_res_3009_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__12_spec__19(v_a_3003_, v_as_3004_, v_i_boxed_3007_, v_stop_boxed_3008_);
    leanh::lean_dec_ref(v_as_3004_);
    leanh::lean_dec(v_a_3003_);
    v_r_3010_ = leanh::lean_box((v_res_3009_) as usize);
    return v_r_3010_;
}
pub unsafe fn l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__12(
    mut v_as_3011_: *mut leanh::LeanObject,
    mut v_a_3012_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: u8 = 0;
    v___x_3013_ = leanh::lean_unsigned_to_nat(0);
    v___x_3014_ = lean_array_get_size(v_as_3011_);
    v___x_3015_ = lean_nat_dec_lt(v___x_3013_, v___x_3014_);
    if v___x_3015_ == 0 {
        return v___x_3015_;
    } else {
        if v___x_3015_ == 0 {
            return v___x_3015_;
        } else {
            let mut v___x_3016_: usize = 0;
            let mut v___x_3017_: usize = 0;
            let mut v___x_3018_: u8 = 0;
            v___x_3016_ = 0usize;
            v___x_3017_ = lean_usize_of_nat(v___x_3014_);
            v___x_3018_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__12_spec__19(v_a_3012_, v_as_3011_, v___x_3016_, v___x_3017_);
            return v___x_3018_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__12___boxed(
    mut v_as_3019_: *mut leanh::LeanObject,
    mut v_a_3020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3021_: u8 = 0;
    let mut v_r_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__12(v_as_3019_, v_a_3020_);
    leanh::lean_dec(v_a_3020_);
    leanh::lean_dec_ref(v_as_3019_);
    v_r_3022_ = leanh::lean_box((v_res_3021_) as usize);
    return v_r_3022_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__13_spec__21(
    mut v_as_3023_: *mut leanh::LeanObject,
    mut v_i_3024_: usize,
    mut v_stop_3025_: usize,
    mut v_b_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: usize = 0;
    let mut v___x_3030_: usize = 0;
    let mut v___x_3032_: u8 = 0;
    let mut v_fst_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: u8 = 0;
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3039_: u8 = 0;
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3044_: u8 = 0;
    let mut v_unused_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3032_ = lean_usize_dec_eq(v_i_3024_, v_stop_3025_);
                if v___x_3032_ == 0 {
                    v_fst_3033_ = leanh::lean_ctor_get(v_b_3026_, 0);
                    v_snd_3034_ = leanh::lean_ctor_get(v_b_3026_, 1);
                    v___x_3035_ = lean_array_uget_borrowed(v_as_3023_, v_i_3024_);
                    v___x_3036_ = lean_name_eq(v___x_3035_, v_fst_3033_);
                    if v___x_3036_ == 0 {
                        leanh::lean_inc(v_snd_3034_);
                        leanh::lean_inc(v_fst_3033_);
                        v_isSharedCheck_3044_ = (!leanh::lean_is_exclusive(v_b_3026_)) as u8;
                        if v_isSharedCheck_3044_ == 0 {
                            v_unused_3045_ = leanh::lean_ctor_get(v_b_3026_, 1);
                            leanh::lean_dec(v_unused_3045_);
                            v_unused_3046_ = leanh::lean_ctor_get(v_b_3026_, 0);
                            leanh::lean_dec(v_unused_3046_);
                            v___x_3038_ = v_b_3026_;
                            v_isShared_3039_ = v_isSharedCheck_3044_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v_b_3026_);
                            v___x_3038_ = leanh::lean_box(0);
                            v_isShared_3039_ = v_isSharedCheck_3044_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_3028_ = v_b_3026_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3026_;
                }
            }
            1 => {
                v___x_3029_ = 1usize;
                v___x_3030_ = lean_usize_add(v_i_3024_, v___x_3029_);
                v_i_3024_ = v___x_3030_;
                v_b_3026_ = v___y_3028_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3040_ = lean_array_push(v_snd_3034_, v_fst_3033_);
                leanh::lean_inc(v___x_3035_);
                if v_isShared_3039_ == 0 {
                    leanh::lean_ctor_set(v___x_3038_, 1, v___x_3040_);
                    leanh::lean_ctor_set(v___x_3038_, 0, v___x_3035_);
                    v___x_3042_ = v___x_3038_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3043_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3043_, 1, v___x_3040_);
                    v___x_3042_ = v_reuseFailAlloc_3043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_3028_ = v___x_3042_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__13_spec__21___boxed(
    mut v_as_3047_: *mut leanh::LeanObject,
    mut v_i_3048_: *mut leanh::LeanObject,
    mut v_stop_3049_: *mut leanh::LeanObject,
    mut v_b_3050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3051_: usize = 0;
    let mut v_stop_boxed_3052_: usize = 0;
    let mut v_res_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3051_ = leanh::lean_unbox_usize(v_i_3048_);
    leanh::lean_dec(v_i_3048_);
    v_stop_boxed_3052_ = leanh::lean_unbox_usize(v_stop_3049_);
    leanh::lean_dec(v_stop_3049_);
    v_res_3053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__13_spec__21(v_as_3047_, v_i_boxed_3051_, v_stop_boxed_3052_, v_b_3050_);
    leanh::lean_dec_ref(v_as_3047_);
    return v_res_3053_;
}
pub unsafe fn l_Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__13(
    mut v_as_3054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: u8 = 0;
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: u8 = 0;
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: usize = 0;
    let mut v___x_3071_: usize = 0;
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: usize = 0;
    let mut v___x_3074_: usize = 0;
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3060_ = leanh::lean_unsigned_to_nat(0);
                v___x_3061_ = lean_array_get_size(v_as_3054_);
                v___x_3062_ = lean_nat_dec_lt(v___x_3060_, v___x_3061_);
                if v___x_3062_ == 0 {
                    v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10___closed__0;
                    return v___x_3063_;
                } else {
                    v___x_3064_ = lean_array_fget_borrowed(v_as_3054_, v___x_3060_);
                    v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10___closed__0;
                    if v___x_3062_ == 0 {
                        leanh::lean_inc(v___x_3064_);
                        v___x_3066_ = lean_array_push(v___x_3065_, v___x_3064_);
                        return v___x_3066_;
                    } else {
                        leanh::lean_inc(v___x_3064_);
                        v___x_3067_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3067_, 0, v___x_3064_);
                        leanh::lean_ctor_set(v___x_3067_, 1, v___x_3065_);
                        v___x_3068_ = lean_nat_dec_le(v___x_3061_, v___x_3061_);
                        if v___x_3068_ == 0 {
                            if v___x_3062_ == 0 {
                                leanh::lean_dec_ref_known(v___x_3067_, 2);
                                leanh::lean_inc(v___x_3064_);
                                v___x_3069_ = lean_array_push(v___x_3065_, v___x_3064_);
                                return v___x_3069_;
                            } else {
                                v___x_3070_ = 0usize;
                                v___x_3071_ = lean_usize_of_nat(v___x_3061_);
                                v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__13_spec__21(v_as_3054_, v___x_3070_, v___x_3071_, v___x_3067_);
                                v___y_3056_ = v___x_3072_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_3073_ = 0usize;
                            v___x_3074_ = lean_usize_of_nat(v___x_3061_);
                            v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__13_spec__21(v_as_3054_, v___x_3073_, v___x_3074_, v___x_3067_);
                            v___y_3056_ = v___x_3075_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3057_ = leanh::lean_ctor_get(v___y_3056_, 0);
                leanh::lean_inc(v_fst_3057_);
                v_snd_3058_ = leanh::lean_ctor_get(v___y_3056_, 1);
                leanh::lean_inc(v_snd_3058_);
                leanh::lean_dec_ref(v___y_3056_);
                v___x_3059_ = lean_array_push(v_snd_3058_, v_fst_3057_);
                return v___x_3059_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__13___boxed(
    mut v_as_3076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3077_ = l_Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__13(v_as_3076_);
    leanh::lean_dec_ref(v_as_3076_);
    return v_res_3077_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__15(
    mut v_sz_3078_: usize,
    mut v_i_3079_: usize,
    mut v_bs_3080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3081_: u8 = 0;
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: usize = 0;
    let mut v___x_3088_: usize = 0;
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3081_ = lean_usize_dec_lt(v_i_3079_, v_sz_3078_);
                if v___x_3081_ == 0 {
                    return v_bs_3080_;
                } else {
                    v___x_3082_ = leanh::lean_unsigned_to_nat(0);
                    v_v_3083_ = lean_array_uget(v_bs_3080_, v_i_3079_);
                    v_bs_x27_3084_ = lean_array_uset(v_bs_3080_, v_i_3079_, v___x_3082_);
                    v___x_3085_ = leanh::lean_box(0);
                    v___x_3086_ = lean_array_get(v___x_3085_, v_v_3083_, v___x_3082_);
                    leanh::lean_dec(v_v_3083_);
                    v___x_3087_ = 1usize;
                    v___x_3088_ = lean_usize_add(v_i_3079_, v___x_3087_);
                    v___x_3089_ = lean_array_uset(v_bs_x27_3084_, v_i_3079_, v___x_3086_);
                    v_i_3079_ = v___x_3088_;
                    v_bs_3080_ = v___x_3089_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__15___boxed(
    mut v_sz_3091_: *mut leanh::LeanObject,
    mut v_i_3092_: *mut leanh::LeanObject,
    mut v_bs_3093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3094_: usize = 0;
    let mut v_i_boxed_3095_: usize = 0;
    let mut v_res_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3094_ = leanh::lean_unbox_usize(v_sz_3091_);
    leanh::lean_dec(v_sz_3091_);
    v_i_boxed_3095_ = leanh::lean_unbox_usize(v_i_3092_);
    leanh::lean_dec(v_i_3092_);
    v_res_3096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__15(v_sz_boxed_3094_, v_i_boxed_3095_, v_bs_3093_);
    return v_res_3096_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11_spec__17(
    mut v_as_3097_: *mut leanh::LeanObject,
    mut v_i_3098_: usize,
    mut v_stop_3099_: usize,
    mut v_b_3100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: usize = 0;
    let mut v___x_3104_: usize = 0;
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: u8 = 0;
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3106_ = lean_usize_dec_eq(v_i_3098_, v_stop_3099_);
                if v___x_3106_ == 0 {
                    v___x_3107_ = lean_array_uget_borrowed(v_as_3097_, v_i_3098_);
                    v___x_3108_ = lean_array_get_size(v___x_3107_);
                    v___x_3109_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3110_ = lean_nat_dec_eq(v___x_3108_, v___x_3109_);
                    if v___x_3110_ == 0 {
                        leanh::lean_inc(v___x_3107_);
                        v___x_3111_ = lean_array_push(v_b_3100_, v___x_3107_);
                        v___y_3102_ = v___x_3111_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3102_ = v_b_3100_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3100_;
                }
            }
            1 => {
                v___x_3103_ = 1usize;
                v___x_3104_ = lean_usize_add(v_i_3098_, v___x_3103_);
                v_i_3098_ = v___x_3104_;
                v_b_3100_ = v___y_3102_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11_spec__17___boxed(
    mut v_as_3112_: *mut leanh::LeanObject,
    mut v_i_3113_: *mut leanh::LeanObject,
    mut v_stop_3114_: *mut leanh::LeanObject,
    mut v_b_3115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3116_: usize = 0;
    let mut v_stop_boxed_3117_: usize = 0;
    let mut v_res_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3116_ = leanh::lean_unbox_usize(v_i_3113_);
    leanh::lean_dec(v_i_3113_);
    v_stop_boxed_3117_ = leanh::lean_unbox_usize(v_stop_3114_);
    leanh::lean_dec(v_stop_3114_);
    v_res_3118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11_spec__17(v_as_3112_, v_i_boxed_3116_, v_stop_boxed_3117_, v_b_3115_);
    leanh::lean_dec_ref(v_as_3112_);
    return v_res_3118_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11(
    mut v_as_3119_: *mut leanh::LeanObject,
    mut v_i_3120_: usize,
    mut v_stop_3121_: usize,
    mut v_b_3122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: usize = 0;
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: u8 = 0;
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: u8 = 0;
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3128_ = lean_usize_dec_eq(v_i_3120_, v_stop_3121_);
                if v___x_3128_ == 0 {
                    v___x_3129_ = lean_array_uget_borrowed(v_as_3119_, v_i_3120_);
                    v___x_3130_ = lean_array_get_size(v___x_3129_);
                    v___x_3131_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3132_ = lean_nat_dec_eq(v___x_3130_, v___x_3131_);
                    if v___x_3132_ == 0 {
                        leanh::lean_inc(v___x_3129_);
                        v___x_3133_ = lean_array_push(v_b_3122_, v___x_3129_);
                        v___y_3124_ = v___x_3133_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3124_ = v_b_3122_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3122_;
                }
            }
            1 => {
                v___x_3125_ = 1usize;
                v___x_3126_ = lean_usize_add(v_i_3120_, v___x_3125_);
                v___x_3127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11_spec__17(v_as_3119_, v___x_3126_, v_stop_3121_, v___y_3124_);
                return v___x_3127_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11___boxed(
    mut v_as_3134_: *mut leanh::LeanObject,
    mut v_i_3135_: *mut leanh::LeanObject,
    mut v_stop_3136_: *mut leanh::LeanObject,
    mut v_b_3137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3138_: usize = 0;
    let mut v_stop_boxed_3139_: usize = 0;
    let mut v_res_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3138_ = leanh::lean_unbox_usize(v_i_3135_);
    leanh::lean_dec(v_i_3135_);
    v_stop_boxed_3139_ = leanh::lean_unbox_usize(v_stop_3136_);
    leanh::lean_dec(v_stop_3136_);
    v_res_3140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11(v_as_3134_, v_i_boxed_3138_, v_stop_boxed_3139_, v_b_3137_);
    leanh::lean_dec_ref(v_as_3134_);
    return v_res_3140_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10_spec__14(
    mut v___x_3141_: *mut leanh::LeanObject,
    mut v_as_3142_: *mut leanh::LeanObject,
    mut v_i_3143_: usize,
    mut v_stop_3144_: usize,
) -> u8 {
    let mut v___x_3145_: u8 = 0;
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: u8 = 0;
    let mut v___y_3155_: u8 = 0;
    let mut v___x_3156_: usize = 0;
    let mut v___x_3157_: usize = 0;
    let mut v___y_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: u8 = 0;
    let mut v___x_3162_: usize = 0;
    let mut v___x_3163_: usize = 0;
    let mut v___x_3164_: u8 = 0;
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: u8 = 0;
    let mut v___x_3168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3145_ = lean_usize_dec_eq(v_i_3143_, v_stop_3144_);
                if v___x_3145_ == 0 {
                    v___x_3146_ = lean_array_uget_borrowed(v_as_3142_, v_i_3143_);
                    v___x_3147_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3148_ = lean_array_get_size(v___x_3146_);
                    leanh::lean_inc(v___x_3146_);
                    v___x_3149_ =
                        l_Array_toSubarray___redArg(v___x_3146_, v___x_3147_, v___x_3148_);
                    v_array_3150_ = leanh::lean_ctor_get(v___x_3149_, 0);
                    leanh::lean_inc_ref(v_array_3150_);
                    v_start_3151_ = leanh::lean_ctor_get(v___x_3149_, 1);
                    leanh::lean_inc(v_start_3151_);
                    v_stop_3152_ = leanh::lean_ctor_get(v___x_3149_, 2);
                    leanh::lean_inc(v_stop_3152_);
                    leanh::lean_dec_ref(v___x_3149_);
                    v___x_3153_ = 1;
                    v___x_3165_ = lean_nat_dec_lt(v_start_3151_, v_stop_3152_);
                    if v___x_3165_ == 0 {
                        leanh::lean_dec(v_stop_3152_);
                        leanh::lean_dec(v_start_3151_);
                        leanh::lean_dec_ref(v_array_3150_);
                        v___y_3155_ = v___x_3145_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3166_ = lean_array_get_size(v_array_3150_);
                        v___x_3167_ = lean_nat_dec_le(v_stop_3152_, v___x_3166_);
                        if v___x_3167_ == 0 {
                            leanh::lean_dec(v_stop_3152_);
                            v___y_3160_ = v___x_3166_;
                            state = 2;
                            continue;
                        } else {
                            v___y_3160_ = v_stop_3152_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_3168_ = 0;
                    return v___x_3168_;
                }
            }
            1 => {
                if v___y_3155_ == 0 {
                    v___x_3156_ = 1usize;
                    v___x_3157_ = lean_usize_add(v_i_3143_, v___x_3156_);
                    v_i_3143_ = v___x_3157_;
                    state = 0;
                    continue;
                } else {
                    return v___x_3153_;
                }
            }
            2 => {
                v___x_3161_ = lean_nat_dec_lt(v_start_3151_, v___y_3160_);
                if v___x_3161_ == 0 {
                    leanh::lean_dec(v___y_3160_);
                    leanh::lean_dec(v_start_3151_);
                    leanh::lean_dec_ref(v_array_3150_);
                    v___y_3155_ = v___x_3145_;
                    state = 1;
                    continue;
                } else {
                    v___x_3162_ = lean_usize_of_nat(v_start_3151_);
                    leanh::lean_dec(v_start_3151_);
                    v___x_3163_ = lean_usize_of_nat(v___y_3160_);
                    leanh::lean_dec(v___y_3160_);
                    v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__8(v___x_3141_, v_array_3150_, v___x_3162_, v___x_3163_);
                    leanh::lean_dec_ref(v_array_3150_);
                    v___y_3155_ = v___x_3164_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10_spec__14___boxed(
    mut v___x_3169_: *mut leanh::LeanObject,
    mut v_as_3170_: *mut leanh::LeanObject,
    mut v_i_3171_: *mut leanh::LeanObject,
    mut v_stop_3172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3173_: usize = 0;
    let mut v_stop_boxed_3174_: usize = 0;
    let mut v_res_3175_: u8 = 0;
    let mut v_r_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3173_ = leanh::lean_unbox_usize(v_i_3171_);
    leanh::lean_dec(v_i_3171_);
    v_stop_boxed_3174_ = leanh::lean_unbox_usize(v_stop_3172_);
    leanh::lean_dec(v_stop_3172_);
    v_res_3175_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10_spec__14(v___x_3169_, v_as_3170_, v_i_boxed_3173_, v_stop_boxed_3174_);
    leanh::lean_dec_ref(v_as_3170_);
    leanh::lean_dec(v___x_3169_);
    v_r_3176_ = leanh::lean_box((v_res_3175_) as usize);
    return v_r_3176_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10(
    mut v___x_3177_: *mut leanh::LeanObject,
    mut v_as_3178_: *mut leanh::LeanObject,
    mut v_i_3179_: usize,
    mut v_stop_3180_: usize,
) -> u8 {
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v___y_3191_: u8 = 0;
    let mut v___x_3192_: usize = 0;
    let mut v___x_3193_: usize = 0;
    let mut v___x_3194_: u8 = 0;
    let mut v___y_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___x_3198_: usize = 0;
    let mut v___x_3199_: usize = 0;
    let mut v___x_3200_: u8 = 0;
    let mut v___x_3201_: u8 = 0;
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: u8 = 0;
    let mut v___x_3204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3181_ = lean_usize_dec_eq(v_i_3179_, v_stop_3180_);
                if v___x_3181_ == 0 {
                    v___x_3182_ = lean_array_uget_borrowed(v_as_3178_, v_i_3179_);
                    v___x_3183_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3184_ = lean_array_get_size(v___x_3182_);
                    leanh::lean_inc(v___x_3182_);
                    v___x_3185_ =
                        l_Array_toSubarray___redArg(v___x_3182_, v___x_3183_, v___x_3184_);
                    v_array_3186_ = leanh::lean_ctor_get(v___x_3185_, 0);
                    leanh::lean_inc_ref(v_array_3186_);
                    v_start_3187_ = leanh::lean_ctor_get(v___x_3185_, 1);
                    leanh::lean_inc(v_start_3187_);
                    v_stop_3188_ = leanh::lean_ctor_get(v___x_3185_, 2);
                    leanh::lean_inc(v_stop_3188_);
                    leanh::lean_dec_ref(v___x_3185_);
                    v___x_3189_ = 1;
                    v___x_3201_ = lean_nat_dec_lt(v_start_3187_, v_stop_3188_);
                    if v___x_3201_ == 0 {
                        leanh::lean_dec(v_stop_3188_);
                        leanh::lean_dec(v_start_3187_);
                        leanh::lean_dec_ref(v_array_3186_);
                        v___y_3191_ = v___x_3181_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3202_ = lean_array_get_size(v_array_3186_);
                        v___x_3203_ = lean_nat_dec_le(v_stop_3188_, v___x_3202_);
                        if v___x_3203_ == 0 {
                            leanh::lean_dec(v_stop_3188_);
                            v___y_3196_ = v___x_3202_;
                            state = 2;
                            continue;
                        } else {
                            v___y_3196_ = v_stop_3188_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_3204_ = 0;
                    return v___x_3204_;
                }
            }
            1 => {
                if v___y_3191_ == 0 {
                    v___x_3192_ = 1usize;
                    v___x_3193_ = lean_usize_add(v_i_3179_, v___x_3192_);
                    v___x_3194_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10_spec__14(v___x_3177_, v_as_3178_, v___x_3193_, v_stop_3180_);
                    return v___x_3194_;
                } else {
                    return v___x_3189_;
                }
            }
            2 => {
                v___x_3197_ = lean_nat_dec_lt(v_start_3187_, v___y_3196_);
                if v___x_3197_ == 0 {
                    leanh::lean_dec(v___y_3196_);
                    leanh::lean_dec(v_start_3187_);
                    leanh::lean_dec_ref(v_array_3186_);
                    v___y_3191_ = v___x_3181_;
                    state = 1;
                    continue;
                } else {
                    v___x_3198_ = lean_usize_of_nat(v_start_3187_);
                    leanh::lean_dec(v_start_3187_);
                    v___x_3199_ = lean_usize_of_nat(v___y_3196_);
                    leanh::lean_dec(v___y_3196_);
                    v___x_3200_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__8(v___x_3177_, v_array_3186_, v___x_3198_, v___x_3199_);
                    leanh::lean_dec_ref(v_array_3186_);
                    v___y_3191_ = v___x_3200_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10___boxed(
    mut v___x_3205_: *mut leanh::LeanObject,
    mut v_as_3206_: *mut leanh::LeanObject,
    mut v_i_3207_: *mut leanh::LeanObject,
    mut v_stop_3208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3209_: usize = 0;
    let mut v_stop_boxed_3210_: usize = 0;
    let mut v_res_3211_: u8 = 0;
    let mut v_r_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3209_ = leanh::lean_unbox_usize(v_i_3207_);
    leanh::lean_dec(v_i_3207_);
    v_stop_boxed_3210_ = leanh::lean_unbox_usize(v_stop_3208_);
    leanh::lean_dec(v_stop_3208_);
    v_res_3211_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10(v___x_3205_, v_as_3206_, v_i_boxed_3209_, v_stop_boxed_3210_);
    leanh::lean_dec_ref(v_as_3206_);
    leanh::lean_dec(v___x_3205_);
    v_r_3212_ = leanh::lean_box((v_res_3211_) as usize);
    return v_r_3212_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__12(
    mut v___x_3213_: *mut leanh::LeanObject,
    mut v___y_3214_: u8,
    mut v_as_3215_: *mut leanh::LeanObject,
    mut v_i_3216_: usize,
    mut v_stop_3217_: usize,
) -> u8 {
    let mut v___x_3218_: u8 = 0;
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: u8 = 0;
    let mut v___y_3228_: u8 = 0;
    let mut v___x_3229_: usize = 0;
    let mut v___x_3230_: usize = 0;
    let mut v___y_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: usize = 0;
    let mut v___x_3236_: usize = 0;
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3238_: u8 = 0;
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: u8 = 0;
    let mut v___x_3241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3218_ = lean_usize_dec_eq(v_i_3216_, v_stop_3217_);
                if v___x_3218_ == 0 {
                    v___x_3219_ = lean_array_uget_borrowed(v_as_3215_, v_i_3216_);
                    v___x_3220_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3221_ = lean_array_get_size(v___x_3219_);
                    leanh::lean_inc(v___x_3219_);
                    v___x_3222_ =
                        l_Array_toSubarray___redArg(v___x_3219_, v___x_3220_, v___x_3221_);
                    v_array_3223_ = leanh::lean_ctor_get(v___x_3222_, 0);
                    leanh::lean_inc_ref(v_array_3223_);
                    v_start_3224_ = leanh::lean_ctor_get(v___x_3222_, 1);
                    leanh::lean_inc(v_start_3224_);
                    v_stop_3225_ = leanh::lean_ctor_get(v___x_3222_, 2);
                    leanh::lean_inc(v_stop_3225_);
                    leanh::lean_dec_ref(v___x_3222_);
                    v___x_3226_ = 1;
                    v___x_3238_ = lean_nat_dec_lt(v_start_3224_, v_stop_3225_);
                    if v___x_3238_ == 0 {
                        leanh::lean_dec(v_stop_3225_);
                        leanh::lean_dec(v_start_3224_);
                        leanh::lean_dec_ref(v_array_3223_);
                        v___y_3228_ = v___x_3218_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3239_ = lean_array_get_size(v_array_3223_);
                        v___x_3240_ = lean_nat_dec_le(v_stop_3225_, v___x_3239_);
                        if v___x_3240_ == 0 {
                            leanh::lean_dec(v_stop_3225_);
                            v___y_3233_ = v___x_3239_;
                            state = 2;
                            continue;
                        } else {
                            v___y_3233_ = v_stop_3225_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_3241_ = 0;
                    return v___x_3241_;
                }
            }
            1 => {
                if v___y_3228_ == 0 {
                    v___x_3229_ = 1usize;
                    v___x_3230_ = lean_usize_add(v_i_3216_, v___x_3229_);
                    v_i_3216_ = v___x_3230_;
                    state = 0;
                    continue;
                } else {
                    return v___x_3226_;
                }
            }
            2 => {
                v___x_3234_ = lean_nat_dec_lt(v_start_3224_, v___y_3233_);
                if v___x_3234_ == 0 {
                    leanh::lean_dec(v___y_3233_);
                    leanh::lean_dec(v_start_3224_);
                    leanh::lean_dec_ref(v_array_3223_);
                    v___y_3228_ = v___x_3218_;
                    state = 1;
                    continue;
                } else {
                    v___x_3235_ = lean_usize_of_nat(v_start_3224_);
                    leanh::lean_dec(v_start_3224_);
                    v___x_3236_ = lean_usize_of_nat(v___y_3233_);
                    leanh::lean_dec(v___y_3233_);
                    v___x_3237_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__8(v___x_3213_, v_array_3223_, v___x_3235_, v___x_3236_);
                    leanh::lean_dec_ref(v_array_3223_);
                    if v___x_3237_ == 0 {
                        v___y_3228_ = v___x_3237_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3228_ = v___y_3214_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__12___boxed(
    mut v___x_3242_: *mut leanh::LeanObject,
    mut v___y_3243_: *mut leanh::LeanObject,
    mut v_as_3244_: *mut leanh::LeanObject,
    mut v_i_3245_: *mut leanh::LeanObject,
    mut v_stop_3246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_15957__boxed_3247_: u8 = 0;
    let mut v_i_boxed_3248_: usize = 0;
    let mut v_stop_boxed_3249_: usize = 0;
    let mut v_res_3250_: u8 = 0;
    let mut v_r_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_15957__boxed_3247_ = (leanh::lean_unbox(v___y_3243_) as u8);
    v_i_boxed_3248_ = leanh::lean_unbox_usize(v_i_3245_);
    leanh::lean_dec(v_i_3245_);
    v_stop_boxed_3249_ = leanh::lean_unbox_usize(v_stop_3246_);
    leanh::lean_dec(v_stop_3246_);
    v_res_3250_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__12(v___x_3242_, v___y_15957__boxed_3247_, v_as_3244_, v_i_boxed_3248_, v_stop_boxed_3249_);
    leanh::lean_dec_ref(v_as_3244_);
    leanh::lean_dec(v___x_3242_);
    v_r_3251_ = leanh::lean_box((v_res_3250_) as usize);
    return v_r_3251_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9(
    mut v___x_3252_: *mut leanh::LeanObject,
    mut v___y_3253_: u8,
    mut v_as_3254_: *mut leanh::LeanObject,
    mut v_i_3255_: usize,
    mut v_stop_3256_: usize,
) -> u8 {
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: u8 = 0;
    let mut v___y_3267_: u8 = 0;
    let mut v___x_3268_: usize = 0;
    let mut v___x_3269_: usize = 0;
    let mut v___x_3270_: u8 = 0;
    let mut v___y_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: u8 = 0;
    let mut v___x_3274_: usize = 0;
    let mut v___x_3275_: usize = 0;
    let mut v___x_3276_: u8 = 0;
    let mut v___x_3277_: u8 = 0;
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3280_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3257_ = lean_usize_dec_eq(v_i_3255_, v_stop_3256_);
                if v___x_3257_ == 0 {
                    v___x_3258_ = lean_array_uget_borrowed(v_as_3254_, v_i_3255_);
                    v___x_3259_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3260_ = lean_array_get_size(v___x_3258_);
                    leanh::lean_inc(v___x_3258_);
                    v___x_3261_ =
                        l_Array_toSubarray___redArg(v___x_3258_, v___x_3259_, v___x_3260_);
                    v_array_3262_ = leanh::lean_ctor_get(v___x_3261_, 0);
                    leanh::lean_inc_ref(v_array_3262_);
                    v_start_3263_ = leanh::lean_ctor_get(v___x_3261_, 1);
                    leanh::lean_inc(v_start_3263_);
                    v_stop_3264_ = leanh::lean_ctor_get(v___x_3261_, 2);
                    leanh::lean_inc(v_stop_3264_);
                    leanh::lean_dec_ref(v___x_3261_);
                    v___x_3265_ = 1;
                    v___x_3277_ = lean_nat_dec_lt(v_start_3263_, v_stop_3264_);
                    if v___x_3277_ == 0 {
                        leanh::lean_dec(v_stop_3264_);
                        leanh::lean_dec(v_start_3263_);
                        leanh::lean_dec_ref(v_array_3262_);
                        v___y_3267_ = v___x_3257_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3278_ = lean_array_get_size(v_array_3262_);
                        v___x_3279_ = lean_nat_dec_le(v_stop_3264_, v___x_3278_);
                        if v___x_3279_ == 0 {
                            leanh::lean_dec(v_stop_3264_);
                            v___y_3272_ = v___x_3278_;
                            state = 2;
                            continue;
                        } else {
                            v___y_3272_ = v_stop_3264_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_3280_ = 0;
                    return v___x_3280_;
                }
            }
            1 => {
                if v___y_3267_ == 0 {
                    v___x_3268_ = 1usize;
                    v___x_3269_ = lean_usize_add(v_i_3255_, v___x_3268_);
                    v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9_spec__12(v___x_3252_, v___y_3253_, v_as_3254_, v___x_3269_, v_stop_3256_);
                    return v___x_3270_;
                } else {
                    return v___x_3265_;
                }
            }
            2 => {
                v___x_3273_ = lean_nat_dec_lt(v_start_3263_, v___y_3272_);
                if v___x_3273_ == 0 {
                    leanh::lean_dec(v___y_3272_);
                    leanh::lean_dec(v_start_3263_);
                    leanh::lean_dec_ref(v_array_3262_);
                    v___y_3267_ = v___x_3257_;
                    state = 1;
                    continue;
                } else {
                    v___x_3274_ = lean_usize_of_nat(v_start_3263_);
                    leanh::lean_dec(v_start_3263_);
                    v___x_3275_ = lean_usize_of_nat(v___y_3272_);
                    leanh::lean_dec(v___y_3272_);
                    v___x_3276_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__8(v___x_3252_, v_array_3262_, v___x_3274_, v___x_3275_);
                    leanh::lean_dec_ref(v_array_3262_);
                    if v___x_3276_ == 0 {
                        v___y_3267_ = v___x_3276_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3267_ = v___y_3253_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9___boxed(
    mut v___x_3281_: *mut leanh::LeanObject,
    mut v___y_3282_: *mut leanh::LeanObject,
    mut v_as_3283_: *mut leanh::LeanObject,
    mut v_i_3284_: *mut leanh::LeanObject,
    mut v_stop_3285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_16005__boxed_3286_: u8 = 0;
    let mut v_i_boxed_3287_: usize = 0;
    let mut v_stop_boxed_3288_: usize = 0;
    let mut v_res_3289_: u8 = 0;
    let mut v_r_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_16005__boxed_3286_ = (leanh::lean_unbox(v___y_3282_) as u8);
    v_i_boxed_3287_ = leanh::lean_unbox_usize(v_i_3284_);
    leanh::lean_dec(v_i_3284_);
    v_stop_boxed_3288_ = leanh::lean_unbox_usize(v_stop_3285_);
    leanh::lean_dec(v_stop_3285_);
    v_res_3289_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9(v___x_3281_, v___y_16005__boxed_3286_, v_as_3283_, v_i_boxed_3287_, v_stop_boxed_3288_);
    leanh::lean_dec_ref(v_as_3283_);
    leanh::lean_dec(v___x_3281_);
    v_r_3290_ = leanh::lean_box((v_res_3289_) as usize);
    return v_r_3290_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___lam__0(
    mut v___x_3291_: *mut leanh::LeanObject,
    mut v___y_3292_: *mut leanh::LeanObject,
    mut v___y_3293_: *mut leanh::LeanObject,
    mut v___y_3294_: *mut leanh::LeanObject,
    mut v___y_3295_: *mut leanh::LeanObject,
    mut v___y_3296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3298_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3298_, 0, v___x_3291_);
    return v___x_3298_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___lam__0___boxed(
    mut v___x_3299_: *mut leanh::LeanObject,
    mut v___y_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
    mut v___y_3302_: *mut leanh::LeanObject,
    mut v___y_3303_: *mut leanh::LeanObject,
    mut v___y_3304_: *mut leanh::LeanObject,
    mut v___y_3305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3306_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___lam__0(v___x_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
    leanh::lean_dec(v___y_3304_);
    leanh::lean_dec_ref(v___y_3303_);
    leanh::lean_dec(v___y_3302_);
    leanh::lean_dec_ref(v___y_3301_);
    leanh::lean_dec(v___y_3300_);
    return v_res_3306_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3307_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_3307_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg(
    mut v_upperBound_3315_: *mut leanh::LeanObject,
    mut v_resOrders_3316_: *mut leanh::LeanObject,
    mut v_next_3317_: *mut leanh::LeanObject,
    mut v___x_3318_: *mut leanh::LeanObject,
    mut v_a_3319_: *mut leanh::LeanObject,
    mut v_b_3320_: *mut leanh::LeanObject,
    mut v___y_3321_: *mut leanh::LeanObject,
    mut v___y_3322_: *mut leanh::LeanObject,
    mut v___y_3323_: *mut leanh::LeanObject,
    mut v___y_3324_: *mut leanh::LeanObject,
    mut v___y_3325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3333_: u8 = 0;
    let mut v_a_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3342_: u8 = 0;
    let mut v_a_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3346_: u8 = 0;
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3350_: u8 = 0;
    let mut v___x_3351_: u8 = 0;
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: u8 = 0;
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: u8 = 0;
    let mut v___y_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: u8 = 0;
    let mut v___x_3379_: usize = 0;
    let mut v___x_3380_: usize = 0;
    let mut v___x_3381_: u8 = 0;
    let mut v___y_3383_: u8 = 0;
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: u8 = 0;
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: u8 = 0;
    let mut v___y_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: usize = 0;
    let mut v___x_3398_: usize = 0;
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3351_ = lean_nat_dec_lt(v_a_3319_, v_upperBound_3315_);
                if v___x_3351_ == 0 {
                    leanh::lean_dec(v_a_3319_);
                    leanh::lean_dec(v___x_3318_);
                    leanh::lean_dec_ref(v_resOrders_3316_);
                    v___x_3352_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3352_, 0, v_b_3320_);
                    return v___x_3352_;
                } else {
                    leanh::lean_dec_ref(v_b_3320_);
                    v___x_3353_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0);
                    v___x_3354_ = leanh::lean_box(0);
                    v___x_3355_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3356_ =
                        lean_array_get_borrowed(v___x_3353_, v_resOrders_3316_, v_a_3319_);
                    v___x_3357_ = lean_array_get_borrowed(v___x_3354_, v___x_3356_, v___x_3355_);
                    leanh::lean_inc(v_a_3319_);
                    leanh::lean_inc_ref(v_resOrders_3316_);
                    v___x_3358_ =
                        l_Array_toSubarray___redArg(v_resOrders_3316_, v___x_3355_, v_a_3319_);
                    v_array_3359_ = leanh::lean_ctor_get(v___x_3358_, 0);
                    leanh::lean_inc_ref(v_array_3359_);
                    v_start_3360_ = leanh::lean_ctor_get(v___x_3358_, 1);
                    leanh::lean_inc(v_start_3360_);
                    v_stop_3361_ = leanh::lean_ctor_get(v___x_3358_, 2);
                    leanh::lean_inc(v_stop_3361_);
                    leanh::lean_dec_ref(v___x_3358_);
                    v___x_3362_ = leanh::lean_box(0);
                    v___x_3393_ = lean_nat_dec_lt(v_start_3360_, v_stop_3361_);
                    if v___x_3393_ == 0 {
                        leanh::lean_dec(v_stop_3361_);
                        leanh::lean_dec(v_start_3360_);
                        leanh::lean_dec_ref(v_array_3359_);
                        v___y_3383_ = v___x_3351_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3400_ = lean_array_get_size(v_array_3359_);
                        v___x_3401_ = lean_nat_dec_le(v_stop_3361_, v___x_3400_);
                        if v___x_3401_ == 0 {
                            leanh::lean_dec(v_stop_3361_);
                            v___y_3395_ = v___x_3400_;
                            state = 10;
                            continue;
                        } else {
                            v___y_3395_ = v_stop_3361_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_3325_);
                leanh::lean_inc_ref(v___y_3324_);
                leanh::lean_inc(v___y_3323_);
                leanh::lean_inc_ref(v___y_3322_);
                leanh::lean_inc(v___y_3321_);
                v___x_3329_ = leanh::lean_apply_6(
                    v___y_3328_,
                    v___y_3321_,
                    v___y_3322_,
                    v___y_3323_,
                    v___y_3324_,
                    v___y_3325_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3329_) == 0 {
                    v_a_3330_ = leanh::lean_ctor_get(v___x_3329_, 0);
                    v_isSharedCheck_3342_ = (!leanh::lean_is_exclusive(v___x_3329_)) as u8;
                    if v_isSharedCheck_3342_ == 0 {
                        v___x_3332_ = v___x_3329_;
                        v_isShared_3333_ = v_isSharedCheck_3342_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3330_);
                        leanh::lean_dec(v___x_3329_);
                        v___x_3332_ = leanh::lean_box(0);
                        v_isShared_3333_ = v_isSharedCheck_3342_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3319_);
                    leanh::lean_dec(v___x_3318_);
                    leanh::lean_dec_ref(v_resOrders_3316_);
                    v_a_3343_ = leanh::lean_ctor_get(v___x_3329_, 0);
                    v_isSharedCheck_3350_ = (!leanh::lean_is_exclusive(v___x_3329_)) as u8;
                    if v_isSharedCheck_3350_ == 0 {
                        v___x_3345_ = v___x_3329_;
                        v_isShared_3346_ = v_isSharedCheck_3350_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3343_);
                        leanh::lean_dec(v___x_3329_);
                        v___x_3345_ = leanh::lean_box(0);
                        v_isShared_3346_ = v_isSharedCheck_3350_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3330_) == 0 {
                    leanh::lean_dec(v_a_3319_);
                    leanh::lean_dec(v___x_3318_);
                    leanh::lean_dec_ref(v_resOrders_3316_);
                    v_a_3334_ = leanh::lean_ctor_get(v_a_3330_, 0);
                    leanh::lean_inc(v_a_3334_);
                    leanh::lean_dec_ref_known(v_a_3330_, 1);
                    if v_isShared_3333_ == 0 {
                        leanh::lean_ctor_set(v___x_3332_, 0, v_a_3334_);
                        v___x_3336_ = v___x_3332_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3337_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3334_);
                        v___x_3336_ = v_reuseFailAlloc_3337_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3332_);
                    v_a_3338_ = leanh::lean_ctor_get(v_a_3330_, 0);
                    leanh::lean_inc(v_a_3338_);
                    leanh::lean_dec_ref_known(v_a_3330_, 1);
                    v___x_3339_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3340_ = lean_nat_add(v_a_3319_, v___x_3339_);
                    leanh::lean_dec(v_a_3319_);
                    v_a_3319_ = v___x_3340_;
                    v_b_3320_ = v_a_3338_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_3336_;
            }
            4 => {
                if v_isShared_3346_ == 0 {
                    v___x_3348_ = v___x_3345_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
                    v___x_3348_ = v_reuseFailAlloc_3349_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3348_;
            }
            6 => {
                v___x_3364_ = lean_nat_dec_eq(v_next_3317_, v___x_3355_);
                v___x_3365_ = leanh::lean_box((v___x_3364_) as usize);
                leanh::lean_inc(v___x_3357_);
                v___x_3366_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3366_, 0, v___x_3365_);
                leanh::lean_ctor_set(v___x_3366_, 1, v___x_3357_);
                v___x_3367_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3367_, 0, v___x_3366_);
                v___x_3368_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3368_, 0, v___x_3367_);
                leanh::lean_ctor_set(v___x_3368_, 1, v___x_3362_);
                v___x_3369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3369_, 0, v___x_3368_);
                v___f_3370_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_3370_, 0, v___x_3369_);
                v___y_3328_ = v___f_3370_;
                state = 1;
                continue;
            }
            7 => {
                v___f_3372_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__3;
                v___y_3328_ = v___f_3372_;
                state = 1;
                continue;
            }
            8 => {
                v___x_3378_ = lean_nat_dec_lt(v___y_3374_, v___y_3377_);
                if v___x_3378_ == 0 {
                    leanh::lean_dec(v___y_3377_);
                    leanh::lean_dec_ref(v___y_3376_);
                    leanh::lean_dec(v___y_3374_);
                    state = 6;
                    continue;
                } else {
                    v___x_3379_ = lean_usize_of_nat(v___y_3374_);
                    leanh::lean_dec(v___y_3374_);
                    v___x_3380_ = lean_usize_of_nat(v___y_3377_);
                    leanh::lean_dec(v___y_3377_);
                    v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9(v___x_3357_, v___y_3375_, v___y_3376_, v___x_3379_, v___x_3380_);
                    leanh::lean_dec_ref(v___y_3376_);
                    if v___x_3381_ == 0 {
                        state = 6;
                        continue;
                    } else {
                        state = 7;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3384_ = leanh::lean_unsigned_to_nat(1);
                v___x_3385_ = lean_nat_add(v_a_3319_, v___x_3384_);
                leanh::lean_inc(v___x_3318_);
                leanh::lean_inc_ref(v_resOrders_3316_);
                v___x_3386_ =
                    l_Array_toSubarray___redArg(v_resOrders_3316_, v___x_3385_, v___x_3318_);
                v_array_3387_ = leanh::lean_ctor_get(v___x_3386_, 0);
                leanh::lean_inc_ref(v_array_3387_);
                v_start_3388_ = leanh::lean_ctor_get(v___x_3386_, 1);
                leanh::lean_inc(v_start_3388_);
                v_stop_3389_ = leanh::lean_ctor_get(v___x_3386_, 2);
                leanh::lean_inc(v_stop_3389_);
                leanh::lean_dec_ref(v___x_3386_);
                v___x_3390_ = lean_nat_dec_lt(v_start_3388_, v_stop_3389_);
                if v___x_3390_ == 0 {
                    leanh::lean_dec(v_stop_3389_);
                    leanh::lean_dec(v_start_3388_);
                    leanh::lean_dec_ref(v_array_3387_);
                    state = 6;
                    continue;
                } else {
                    v___x_3391_ = lean_array_get_size(v_array_3387_);
                    v___x_3392_ = lean_nat_dec_le(v_stop_3389_, v___x_3391_);
                    if v___x_3392_ == 0 {
                        leanh::lean_dec(v_stop_3389_);
                        v___y_3374_ = v_start_3388_;
                        v___y_3375_ = v___y_3383_;
                        v___y_3376_ = v_array_3387_;
                        v___y_3377_ = v___x_3391_;
                        state = 8;
                        continue;
                    } else {
                        v___y_3374_ = v_start_3388_;
                        v___y_3375_ = v___y_3383_;
                        v___y_3376_ = v_array_3387_;
                        v___y_3377_ = v_stop_3389_;
                        state = 8;
                        continue;
                    }
                }
            }
            10 => {
                v___x_3396_ = lean_nat_dec_lt(v_start_3360_, v___y_3395_);
                if v___x_3396_ == 0 {
                    leanh::lean_dec(v___y_3395_);
                    leanh::lean_dec(v_start_3360_);
                    leanh::lean_dec_ref(v_array_3359_);
                    v___y_3383_ = v___x_3393_;
                    state = 9;
                    continue;
                } else {
                    v___x_3397_ = lean_usize_of_nat(v_start_3360_);
                    leanh::lean_dec(v_start_3360_);
                    v___x_3398_ = lean_usize_of_nat(v___y_3395_);
                    leanh::lean_dec(v___y_3395_);
                    v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10(v___x_3357_, v_array_3359_, v___x_3397_, v___x_3398_);
                    leanh::lean_dec_ref(v_array_3359_);
                    if v___x_3399_ == 0 {
                        v___y_3383_ = v___x_3396_;
                        state = 9;
                        continue;
                    } else {
                        state = 7;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___boxed(
    mut v_upperBound_3402_: *mut leanh::LeanObject,
    mut v_resOrders_3403_: *mut leanh::LeanObject,
    mut v_next_3404_: *mut leanh::LeanObject,
    mut v___x_3405_: *mut leanh::LeanObject,
    mut v_a_3406_: *mut leanh::LeanObject,
    mut v_b_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
    mut v___y_3413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3414_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg(v_upperBound_3402_, v_resOrders_3403_, v_next_3404_, v___x_3405_, v_a_3406_, v_b_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
    leanh::lean_dec(v___y_3412_);
    leanh::lean_dec_ref(v___y_3411_);
    leanh::lean_dec(v___y_3410_);
    leanh::lean_dec_ref(v___y_3409_);
    leanh::lean_dec(v___y_3408_);
    leanh::lean_dec(v_next_3404_);
    leanh::lean_dec(v_upperBound_3402_);
    return v_res_3414_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(
    mut v_upperBound_3415_: *mut leanh::LeanObject,
    mut v_resOrders_3416_: *mut leanh::LeanObject,
    mut v_next_3417_: *mut leanh::LeanObject,
    mut v___x_3418_: *mut leanh::LeanObject,
    mut v_a_3419_: *mut leanh::LeanObject,
    mut v_b_3420_: *mut leanh::LeanObject,
    mut v___y_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v_a_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3442_: u8 = 0;
    let mut v_a_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3446_: u8 = 0;
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3450_: u8 = 0;
    let mut v___x_3451_: u8 = 0;
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u8 = 0;
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3476_: u8 = 0;
    let mut v___y_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: usize = 0;
    let mut v___x_3480_: usize = 0;
    let mut v___x_3481_: u8 = 0;
    let mut v___y_3483_: u8 = 0;
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: u8 = 0;
    let mut v___x_3493_: u8 = 0;
    let mut v___y_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3497_: usize = 0;
    let mut v___x_3498_: usize = 0;
    let mut v___x_3499_: u8 = 0;
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3451_ = lean_nat_dec_lt(v_a_3419_, v_upperBound_3415_);
                if v___x_3451_ == 0 {
                    leanh::lean_dec(v_a_3419_);
                    leanh::lean_dec(v___x_3418_);
                    leanh::lean_dec_ref(v_resOrders_3416_);
                    v___x_3452_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3452_, 0, v_b_3420_);
                    return v___x_3452_;
                } else {
                    leanh::lean_dec_ref(v_b_3420_);
                    v___x_3453_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0);
                    v___x_3454_ = leanh::lean_box(0);
                    v___x_3455_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3456_ =
                        lean_array_get_borrowed(v___x_3453_, v_resOrders_3416_, v_a_3419_);
                    v___x_3457_ = lean_array_get_borrowed(v___x_3454_, v___x_3456_, v___x_3455_);
                    leanh::lean_inc(v_a_3419_);
                    leanh::lean_inc_ref(v_resOrders_3416_);
                    v___x_3458_ =
                        l_Array_toSubarray___redArg(v_resOrders_3416_, v___x_3455_, v_a_3419_);
                    v_array_3459_ = leanh::lean_ctor_get(v___x_3458_, 0);
                    leanh::lean_inc_ref(v_array_3459_);
                    v_start_3460_ = leanh::lean_ctor_get(v___x_3458_, 1);
                    leanh::lean_inc(v_start_3460_);
                    v_stop_3461_ = leanh::lean_ctor_get(v___x_3458_, 2);
                    leanh::lean_inc(v_stop_3461_);
                    leanh::lean_dec_ref(v___x_3458_);
                    v___x_3462_ = leanh::lean_box(0);
                    v___x_3493_ = lean_nat_dec_lt(v_start_3460_, v_stop_3461_);
                    if v___x_3493_ == 0 {
                        leanh::lean_dec(v_stop_3461_);
                        leanh::lean_dec(v_start_3460_);
                        leanh::lean_dec_ref(v_array_3459_);
                        v___y_3483_ = v___x_3451_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3500_ = lean_array_get_size(v_array_3459_);
                        v___x_3501_ = lean_nat_dec_le(v_stop_3461_, v___x_3500_);
                        if v___x_3501_ == 0 {
                            leanh::lean_dec(v_stop_3461_);
                            v___y_3495_ = v___x_3500_;
                            state = 10;
                            continue;
                        } else {
                            v___y_3495_ = v_stop_3461_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___y_3425_);
                leanh::lean_inc_ref(v___y_3424_);
                leanh::lean_inc(v___y_3423_);
                leanh::lean_inc_ref(v___y_3422_);
                leanh::lean_inc(v___y_3421_);
                v___x_3429_ = leanh::lean_apply_6(
                    v___y_3428_,
                    v___y_3421_,
                    v___y_3422_,
                    v___y_3423_,
                    v___y_3424_,
                    v___y_3425_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_3429_) == 0 {
                    v_a_3430_ = leanh::lean_ctor_get(v___x_3429_, 0);
                    v_isSharedCheck_3442_ = (!leanh::lean_is_exclusive(v___x_3429_)) as u8;
                    if v_isSharedCheck_3442_ == 0 {
                        v___x_3432_ = v___x_3429_;
                        v_isShared_3433_ = v_isSharedCheck_3442_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3430_);
                        leanh::lean_dec(v___x_3429_);
                        v___x_3432_ = leanh::lean_box(0);
                        v_isShared_3433_ = v_isSharedCheck_3442_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3419_);
                    leanh::lean_dec(v___x_3418_);
                    leanh::lean_dec_ref(v_resOrders_3416_);
                    v_a_3443_ = leanh::lean_ctor_get(v___x_3429_, 0);
                    v_isSharedCheck_3450_ = (!leanh::lean_is_exclusive(v___x_3429_)) as u8;
                    if v_isSharedCheck_3450_ == 0 {
                        v___x_3445_ = v___x_3429_;
                        v_isShared_3446_ = v_isSharedCheck_3450_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3443_);
                        leanh::lean_dec(v___x_3429_);
                        v___x_3445_ = leanh::lean_box(0);
                        v_isShared_3446_ = v_isSharedCheck_3450_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_3430_) == 0 {
                    leanh::lean_dec(v_a_3419_);
                    leanh::lean_dec(v___x_3418_);
                    leanh::lean_dec_ref(v_resOrders_3416_);
                    v_a_3434_ = leanh::lean_ctor_get(v_a_3430_, 0);
                    leanh::lean_inc(v_a_3434_);
                    leanh::lean_dec_ref_known(v_a_3430_, 1);
                    if v_isShared_3433_ == 0 {
                        leanh::lean_ctor_set(v___x_3432_, 0, v_a_3434_);
                        v___x_3436_ = v___x_3432_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3437_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3434_);
                        v___x_3436_ = v_reuseFailAlloc_3437_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3432_);
                    v_a_3438_ = leanh::lean_ctor_get(v_a_3430_, 0);
                    leanh::lean_inc(v_a_3438_);
                    leanh::lean_dec_ref_known(v_a_3430_, 1);
                    v___x_3439_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3440_ = lean_nat_add(v_a_3419_, v___x_3439_);
                    leanh::lean_dec(v_a_3419_);
                    v___x_3441_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg(v_upperBound_3415_, v_resOrders_3416_, v_next_3417_, v___x_3418_, v___x_3440_, v_a_3438_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
                    return v___x_3441_;
                }
            }
            3 => {
                return v___x_3436_;
            }
            4 => {
                if v_isShared_3446_ == 0 {
                    v___x_3448_ = v___x_3445_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
                    v___x_3448_ = v_reuseFailAlloc_3449_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3448_;
            }
            6 => {
                v___x_3464_ = lean_nat_dec_eq(v_next_3417_, v___x_3455_);
                v___x_3465_ = leanh::lean_box((v___x_3464_) as usize);
                leanh::lean_inc(v___x_3457_);
                v___x_3466_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3466_, 0, v___x_3465_);
                leanh::lean_ctor_set(v___x_3466_, 1, v___x_3457_);
                v___x_3467_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3467_, 0, v___x_3466_);
                v___x_3468_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3468_, 0, v___x_3467_);
                leanh::lean_ctor_set(v___x_3468_, 1, v___x_3462_);
                v___x_3469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3469_, 0, v___x_3468_);
                v___f_3470_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_3470_, 0, v___x_3469_);
                v___y_3428_ = v___f_3470_;
                state = 1;
                continue;
            }
            7 => {
                v___f_3472_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__3;
                v___y_3428_ = v___f_3472_;
                state = 1;
                continue;
            }
            8 => {
                v___x_3478_ = lean_nat_dec_lt(v___y_3474_, v___y_3477_);
                if v___x_3478_ == 0 {
                    leanh::lean_dec(v___y_3477_);
                    leanh::lean_dec_ref(v___y_3475_);
                    leanh::lean_dec(v___y_3474_);
                    state = 6;
                    continue;
                } else {
                    v___x_3479_ = lean_usize_of_nat(v___y_3474_);
                    leanh::lean_dec(v___y_3474_);
                    v___x_3480_ = lean_usize_of_nat(v___y_3477_);
                    leanh::lean_dec(v___y_3477_);
                    v___x_3481_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__9(v___x_3457_, v___y_3476_, v___y_3475_, v___x_3479_, v___x_3480_);
                    leanh::lean_dec_ref(v___y_3475_);
                    if v___x_3481_ == 0 {
                        state = 6;
                        continue;
                    } else {
                        state = 7;
                        continue;
                    }
                }
            }
            9 => {
                v___x_3484_ = leanh::lean_unsigned_to_nat(1);
                v___x_3485_ = lean_nat_add(v_a_3419_, v___x_3484_);
                leanh::lean_inc(v___x_3418_);
                leanh::lean_inc_ref(v_resOrders_3416_);
                v___x_3486_ =
                    l_Array_toSubarray___redArg(v_resOrders_3416_, v___x_3485_, v___x_3418_);
                v_array_3487_ = leanh::lean_ctor_get(v___x_3486_, 0);
                leanh::lean_inc_ref(v_array_3487_);
                v_start_3488_ = leanh::lean_ctor_get(v___x_3486_, 1);
                leanh::lean_inc(v_start_3488_);
                v_stop_3489_ = leanh::lean_ctor_get(v___x_3486_, 2);
                leanh::lean_inc(v_stop_3489_);
                leanh::lean_dec_ref(v___x_3486_);
                v___x_3490_ = lean_nat_dec_lt(v_start_3488_, v_stop_3489_);
                if v___x_3490_ == 0 {
                    leanh::lean_dec(v_stop_3489_);
                    leanh::lean_dec(v_start_3488_);
                    leanh::lean_dec_ref(v_array_3487_);
                    state = 6;
                    continue;
                } else {
                    v___x_3491_ = lean_array_get_size(v_array_3487_);
                    v___x_3492_ = lean_nat_dec_le(v_stop_3489_, v___x_3491_);
                    if v___x_3492_ == 0 {
                        leanh::lean_dec(v_stop_3489_);
                        v___y_3474_ = v_start_3488_;
                        v___y_3475_ = v_array_3487_;
                        v___y_3476_ = v___y_3483_;
                        v___y_3477_ = v___x_3491_;
                        state = 8;
                        continue;
                    } else {
                        v___y_3474_ = v_start_3488_;
                        v___y_3475_ = v_array_3487_;
                        v___y_3476_ = v___y_3483_;
                        v___y_3477_ = v_stop_3489_;
                        state = 8;
                        continue;
                    }
                }
            }
            10 => {
                v___x_3496_ = lean_nat_dec_lt(v_start_3460_, v___y_3495_);
                if v___x_3496_ == 0 {
                    leanh::lean_dec(v___y_3495_);
                    leanh::lean_dec(v_start_3460_);
                    leanh::lean_dec_ref(v_array_3459_);
                    v___y_3483_ = v___x_3493_;
                    state = 9;
                    continue;
                } else {
                    v___x_3497_ = lean_usize_of_nat(v_start_3460_);
                    leanh::lean_dec(v_start_3460_);
                    v___x_3498_ = lean_usize_of_nat(v___y_3495_);
                    leanh::lean_dec(v___y_3495_);
                    v___x_3499_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__10(v___x_3457_, v_array_3459_, v___x_3497_, v___x_3498_);
                    leanh::lean_dec_ref(v_array_3459_);
                    if v___x_3499_ == 0 {
                        v___y_3483_ = v___x_3496_;
                        state = 9;
                        continue;
                    } else {
                        state = 7;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg___boxed(
    mut v_upperBound_3502_: *mut leanh::LeanObject,
    mut v_resOrders_3503_: *mut leanh::LeanObject,
    mut v_next_3504_: *mut leanh::LeanObject,
    mut v___x_3505_: *mut leanh::LeanObject,
    mut v_a_3506_: *mut leanh::LeanObject,
    mut v_b_3507_: *mut leanh::LeanObject,
    mut v___y_3508_: *mut leanh::LeanObject,
    mut v___y_3509_: *mut leanh::LeanObject,
    mut v___y_3510_: *mut leanh::LeanObject,
    mut v___y_3511_: *mut leanh::LeanObject,
    mut v___y_3512_: *mut leanh::LeanObject,
    mut v___y_3513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3514_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_upperBound_3502_, v_resOrders_3503_, v_next_3504_, v___x_3505_, v_a_3506_, v_b_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
    leanh::lean_dec(v___y_3512_);
    leanh::lean_dec_ref(v___y_3511_);
    leanh::lean_dec(v___y_3510_);
    leanh::lean_dec_ref(v___y_3509_);
    leanh::lean_dec(v___y_3508_);
    leanh::lean_dec(v_next_3504_);
    leanh::lean_dec(v_upperBound_3502_);
    return v_res_3514_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__12___redArg(
    mut v_upperBound_3515_: *mut leanh::LeanObject,
    mut v___x_3516_: *mut leanh::LeanObject,
    mut v_resOrders_3517_: *mut leanh::LeanObject,
    mut v_a_3518_: *mut leanh::LeanObject,
    mut v_b_3519_: *mut leanh::LeanObject,
    mut v___y_3520_: *mut leanh::LeanObject,
    mut v___y_3521_: *mut leanh::LeanObject,
    mut v___y_3522_: *mut leanh::LeanObject,
    mut v___y_3523_: *mut leanh::LeanObject,
    mut v___y_3524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3526_: u8 = 0;
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v_fst_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3540_: u8 = 0;
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3550_: u8 = 0;
    let mut v_unused_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3526_ = lean_nat_dec_lt(v_a_3518_, v_upperBound_3515_);
                if v___x_3526_ == 0 {
                    leanh::lean_dec(v_a_3518_);
                    leanh::lean_dec_ref(v_resOrders_3517_);
                    v___x_3527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3527_, 0, v_b_3519_);
                    return v___x_3527_;
                } else {
                    leanh::lean_dec_ref(v_b_3519_);
                    v___x_3528_ = leanh::lean_box(0);
                    v___x_3529_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__1;
                    v___x_3530_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3531_ = lean_nat_sub(v___x_3516_, v_a_3518_);
                    leanh::lean_inc_ref(v_resOrders_3517_);
                    leanh::lean_inc(v___x_3531_);
                    v___x_3532_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v___x_3531_, v_resOrders_3517_, v_a_3518_, v___x_3531_, v___x_3530_, v___x_3529_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_);
                    leanh::lean_dec(v___x_3531_);
                    if leanh::lean_obj_tag(v___x_3532_) == 0 {
                        v_a_3533_ = leanh::lean_ctor_get(v___x_3532_, 0);
                        v_isSharedCheck_3552_ =
                            (!leanh::lean_is_exclusive(v___x_3532_)) as u8;
                        if v_isSharedCheck_3552_ == 0 {
                            v___x_3535_ = v___x_3532_;
                            v_isShared_3536_ = v_isSharedCheck_3552_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3533_);
                            leanh::lean_dec(v___x_3532_);
                            v___x_3535_ = leanh::lean_box(0);
                            v_isShared_3536_ = v_isSharedCheck_3552_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3518_);
                        leanh::lean_dec_ref(v_resOrders_3517_);
                        return v___x_3532_;
                    }
                }
            }
            1 => {
                v_fst_3537_ = leanh::lean_ctor_get(v_a_3533_, 0);
                v_isSharedCheck_3550_ = (!leanh::lean_is_exclusive(v_a_3533_)) as u8;
                if v_isSharedCheck_3550_ == 0 {
                    v_unused_3551_ = leanh::lean_ctor_get(v_a_3533_, 1);
                    leanh::lean_dec(v_unused_3551_);
                    v___x_3539_ = v_a_3533_;
                    v_isShared_3540_ = v_isSharedCheck_3550_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_3537_);
                    leanh::lean_dec(v_a_3533_);
                    v___x_3539_ = leanh::lean_box(0);
                    v_isShared_3540_ = v_isSharedCheck_3550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_fst_3537_) == 0 {
                    leanh::lean_del_object(v___x_3539_);
                    leanh::lean_del_object(v___x_3535_);
                    v___x_3541_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3542_ = lean_nat_add(v_a_3518_, v___x_3541_);
                    leanh::lean_dec(v_a_3518_);
                    v_a_3518_ = v___x_3542_;
                    v_b_3519_ = v___x_3529_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_3518_);
                    leanh::lean_dec_ref(v_resOrders_3517_);
                    if v_isShared_3540_ == 0 {
                        leanh::lean_ctor_set(v___x_3539_, 1, v___x_3528_);
                        v___x_3545_ = v___x_3539_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3549_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_fst_3537_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3549_, 1, v___x_3528_);
                        v___x_3545_ = v_reuseFailAlloc_3549_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3536_ == 0 {
                    leanh::lean_ctor_set(v___x_3535_, 0, v___x_3545_);
                    v___x_3547_ = v___x_3535_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3548_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3545_);
                    v___x_3547_ = v_reuseFailAlloc_3548_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__12___redArg___boxed(
    mut v_upperBound_3553_: *mut leanh::LeanObject,
    mut v___x_3554_: *mut leanh::LeanObject,
    mut v_resOrders_3555_: *mut leanh::LeanObject,
    mut v_a_3556_: *mut leanh::LeanObject,
    mut v_b_3557_: *mut leanh::LeanObject,
    mut v___y_3558_: *mut leanh::LeanObject,
    mut v___y_3559_: *mut leanh::LeanObject,
    mut v___y_3560_: *mut leanh::LeanObject,
    mut v___y_3561_: *mut leanh::LeanObject,
    mut v___y_3562_: *mut leanh::LeanObject,
    mut v___y_3563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3564_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__12___redArg(v_upperBound_3553_, v___x_3554_, v_resOrders_3555_, v_a_3556_, v_b_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
    leanh::lean_dec(v___y_3562_);
    leanh::lean_dec_ref(v___y_3561_);
    leanh::lean_dec(v___y_3560_);
    leanh::lean_dec_ref(v___y_3559_);
    leanh::lean_dec(v___y_3558_);
    leanh::lean_dec(v___x_3554_);
    leanh::lean_dec(v_upperBound_3553_);
    return v_res_3564_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7(
    mut v_resOrders_3565_: *mut leanh::LeanObject,
    mut v___y_3566_: *mut leanh::LeanObject,
    mut v___y_3567_: *mut leanh::LeanObject,
    mut v___y_3568_: *mut leanh::LeanObject,
    mut v___y_3569_: *mut leanh::LeanObject,
    mut v___y_3570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3579_: u8 = 0;
    let mut v_fst_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3583_: u8 = 0;
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut v_unused_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3602_: u8 = 0;
    let mut v_a_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3606_: u8 = 0;
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3572_ = lean_array_get_size(v_resOrders_3565_);
                v___x_3573_ = leanh::lean_unsigned_to_nat(0);
                v___x_3574_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__1;
                leanh::lean_inc_ref(v_resOrders_3565_);
                v___x_3575_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__12___redArg(v___x_3572_, v___x_3572_, v_resOrders_3565_, v___x_3573_, v___x_3574_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
                if leanh::lean_obj_tag(v___x_3575_) == 0 {
                    v_a_3576_ = leanh::lean_ctor_get(v___x_3575_, 0);
                    v_isSharedCheck_3602_ = (!leanh::lean_is_exclusive(v___x_3575_)) as u8;
                    if v_isSharedCheck_3602_ == 0 {
                        v___x_3578_ = v___x_3575_;
                        v_isShared_3579_ = v_isSharedCheck_3602_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3576_);
                        leanh::lean_dec(v___x_3575_);
                        v___x_3578_ = leanh::lean_box(0);
                        v_isShared_3579_ = v_isSharedCheck_3602_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_resOrders_3565_);
                    v_a_3603_ = leanh::lean_ctor_get(v___x_3575_, 0);
                    v_isSharedCheck_3610_ = (!leanh::lean_is_exclusive(v___x_3575_)) as u8;
                    if v_isSharedCheck_3610_ == 0 {
                        v___x_3605_ = v___x_3575_;
                        v_isShared_3606_ = v_isSharedCheck_3610_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3603_);
                        leanh::lean_dec(v___x_3575_);
                        v___x_3605_ = leanh::lean_box(0);
                        v_isShared_3606_ = v_isSharedCheck_3610_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3580_ = leanh::lean_ctor_get(v_a_3576_, 0);
                v_isSharedCheck_3600_ = (!leanh::lean_is_exclusive(v_a_3576_)) as u8;
                if v_isSharedCheck_3600_ == 0 {
                    v_unused_3601_ = leanh::lean_ctor_get(v_a_3576_, 1);
                    leanh::lean_dec(v_unused_3601_);
                    v___x_3582_ = v_a_3576_;
                    v_isShared_3583_ = v_isSharedCheck_3600_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_3580_);
                    leanh::lean_dec(v_a_3576_);
                    v___x_3582_ = leanh::lean_box(0);
                    v_isShared_3583_ = v_isSharedCheck_3600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_fst_3580_) == 0 {
                    v___x_3584_ = leanh::lean_box(0);
                    v___x_3585_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0_once), _init_l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg___closed__0);
                    v___x_3586_ = 0;
                    v___x_3587_ = lean_array_get(v___x_3585_, v_resOrders_3565_, v___x_3573_);
                    leanh::lean_dec_ref(v_resOrders_3565_);
                    v___x_3588_ = lean_array_get(v___x_3584_, v___x_3587_, v___x_3573_);
                    leanh::lean_dec(v___x_3587_);
                    v___x_3589_ = leanh::lean_box((v___x_3586_) as usize);
                    if v_isShared_3583_ == 0 {
                        leanh::lean_ctor_set(v___x_3582_, 1, v___x_3588_);
                        leanh::lean_ctor_set(v___x_3582_, 0, v___x_3589_);
                        v___x_3591_ = v___x_3582_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3595_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3589_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3595_, 1, v___x_3588_);
                        v___x_3591_ = v_reuseFailAlloc_3595_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3582_);
                    leanh::lean_dec_ref(v_resOrders_3565_);
                    v_val_3596_ = leanh::lean_ctor_get(v_fst_3580_, 0);
                    leanh::lean_inc(v_val_3596_);
                    leanh::lean_dec_ref_known(v_fst_3580_, 1);
                    if v_isShared_3579_ == 0 {
                        leanh::lean_ctor_set(v___x_3578_, 0, v_val_3596_);
                        v___x_3598_ = v___x_3578_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3599_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_val_3596_);
                        v___x_3598_ = v_reuseFailAlloc_3599_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3579_ == 0 {
                    leanh::lean_ctor_set(v___x_3578_, 0, v___x_3591_);
                    v___x_3593_ = v___x_3578_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3591_);
                    v___x_3593_ = v_reuseFailAlloc_3594_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3593_;
            }
            5 => {
                return v___x_3598_;
            }
            6 => {
                if v_isShared_3606_ == 0 {
                    v___x_3608_ = v___x_3605_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3609_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
                    v___x_3608_ = v_reuseFailAlloc_3609_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(
    mut v_resOrders_3611_: *mut leanh::LeanObject,
    mut v___y_3612_: *mut leanh::LeanObject,
    mut v___y_3613_: *mut leanh::LeanObject,
    mut v___y_3614_: *mut leanh::LeanObject,
    mut v___y_3615_: *mut leanh::LeanObject,
    mut v___y_3616_: *mut leanh::LeanObject,
    mut v___y_3617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3618_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7(v_resOrders_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
    leanh::lean_dec(v___y_3616_);
    leanh::lean_dec_ref(v___y_3615_);
    leanh::lean_dec(v___y_3614_);
    leanh::lean_dec_ref(v___y_3613_);
    leanh::lean_dec(v___y_3612_);
    return v_res_3618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__14(
    mut v_parentNames_3619_: *mut leanh::LeanObject,
    mut v_sz_3620_: usize,
    mut v_i_3621_: usize,
    mut v_bs_3622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3623_: u8 = 0;
    let mut v_v_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: u8 = 0;
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: usize = 0;
    let mut v___x_3631_: usize = 0;
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3623_ = lean_usize_dec_lt(v_i_3621_, v_sz_3620_);
                if v___x_3623_ == 0 {
                    return v_bs_3622_;
                } else {
                    v_v_3624_ = lean_array_uget(v_bs_3622_, v_i_3621_);
                    v___x_3625_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3626_ = lean_array_uset(v_bs_3622_, v_i_3621_, v___x_3625_);
                    v___x_3627_ = l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__12(v_parentNames_3619_, v_v_3624_);
                    v___x_3628_ = leanh::lean_box((v___x_3627_) as usize);
                    v___x_3629_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3629_, 0, v___x_3628_);
                    leanh::lean_ctor_set(v___x_3629_, 1, v_v_3624_);
                    v___x_3630_ = 1usize;
                    v___x_3631_ = lean_usize_add(v_i_3621_, v___x_3630_);
                    v___x_3632_ = lean_array_uset(v_bs_x27_3626_, v_i_3621_, v___x_3629_);
                    v_i_3621_ = v___x_3631_;
                    v_bs_3622_ = v___x_3632_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__14___boxed(
    mut v_parentNames_3634_: *mut leanh::LeanObject,
    mut v_sz_3635_: *mut leanh::LeanObject,
    mut v_i_3636_: *mut leanh::LeanObject,
    mut v_bs_3637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3638_: usize = 0;
    let mut v_i_boxed_3639_: usize = 0;
    let mut v_res_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3638_ = leanh::lean_unbox_usize(v_sz_3635_);
    leanh::lean_dec(v_sz_3635_);
    v_i_boxed_3639_ = leanh::lean_unbox_usize(v_i_3636_);
    leanh::lean_dec(v_i_3636_);
    v_res_3640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__14(v_parentNames_3634_, v_sz_boxed_3638_, v_i_boxed_3639_, v_bs_3637_);
    leanh::lean_dec_ref(v_parentNames_3634_);
    return v_res_3640_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg(
    mut v_relaxed_3643_: u8,
    mut v_parentNames_3644_: *mut leanh::LeanObject,
    mut v_a_3645_: *mut leanh::LeanObject,
    mut v___y_3646_: *mut leanh::LeanObject,
    mut v___y_3647_: *mut leanh::LeanObject,
    mut v___y_3648_: *mut leanh::LeanObject,
    mut v___y_3649_: *mut leanh::LeanObject,
    mut v___y_3650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v_fst_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3661_: u8 = 0;
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: u8 = 0;
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defects_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3683_: usize = 0;
    let mut v___x_3684_: usize = 0;
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: u8 = 0;
    let mut v___x_3690_: usize = 0;
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: usize = 0;
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: u8 = 0;
    let mut v_sz_3698_: usize = 0;
    let mut v___x_3699_: usize = 0;
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: u8 = 0;
    let mut v___x_3715_: u8 = 0;
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3719_: usize = 0;
    let mut v___x_3720_: usize = 0;
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: u8 = 0;
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: u8 = 0;
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: u8 = 0;
    let mut v___x_3728_: u8 = 0;
    let mut v___x_3729_: usize = 0;
    let mut v___x_3730_: usize = 0;
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: usize = 0;
    let mut v___x_3733_: usize = 0;
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3738_: u8 = 0;
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3750_: u8 = 0;
    let mut v_isSharedCheck_3751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3652_ = leanh::lean_ctor_get(v_a_3645_, 1);
                v_fst_3653_ = leanh::lean_ctor_get(v_a_3645_, 0);
                v_isSharedCheck_3751_ = (!leanh::lean_is_exclusive(v_a_3645_)) as u8;
                if v_isSharedCheck_3751_ == 0 {
                    v___x_3655_ = v_a_3645_;
                    v_isShared_3656_ = v_isSharedCheck_3751_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3652_);
                    leanh::lean_inc(v_fst_3653_);
                    leanh::lean_dec(v_a_3645_);
                    v___x_3655_ = leanh::lean_box(0);
                    v_isShared_3656_ = v_isSharedCheck_3751_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3657_ = leanh::lean_ctor_get(v_snd_3652_, 0);
                v_snd_3658_ = leanh::lean_ctor_get(v_snd_3652_, 1);
                v_isSharedCheck_3750_ = (!leanh::lean_is_exclusive(v_snd_3652_)) as u8;
                if v_isSharedCheck_3750_ == 0 {
                    v___x_3660_ = v_snd_3652_;
                    v_isShared_3661_ = v_isSharedCheck_3750_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3658_);
                    leanh::lean_inc(v_fst_3657_);
                    leanh::lean_dec(v_snd_3652_);
                    v___x_3660_ = leanh::lean_box(0);
                    v_isShared_3661_ = v_isSharedCheck_3750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3662_ = leanh::lean_unsigned_to_nat(0);
                v___x_3663_ = lean_array_get_size(v_fst_3653_);
                v___x_3664_ = lean_nat_dec_eq(v___x_3663_, v___x_3662_);
                if v___x_3664_ == 0 {
                    leanh::lean_inc(v_fst_3653_);
                    v___x_3665_ = l___private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7(v_fst_3653_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
                    if leanh::lean_obj_tag(v___x_3665_) == 0 {
                        v_a_3666_ = leanh::lean_ctor_get(v___x_3665_, 0);
                        leanh::lean_inc(v_a_3666_);
                        leanh::lean_dec_ref_known(v___x_3665_, 1);
                        v_fst_3678_ = leanh::lean_ctor_get(v_a_3666_, 0);
                        leanh::lean_inc(v_fst_3678_);
                        v_snd_3679_ = leanh::lean_ctor_get(v_a_3666_, 1);
                        leanh::lean_inc(v_snd_3679_);
                        leanh::lean_dec(v_a_3666_);
                        v___x_3715_ = (leanh::lean_unbox(v_fst_3678_) as u8);
                        leanh::lean_dec(v_fst_3678_);
                        if v___x_3715_ == 0 {
                            if v_relaxed_3643_ == 0 {
                                v___x_3716_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3726_ = l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg___closed__0;
                                v___x_3727_ = lean_nat_dec_lt(v___x_3662_, v___x_3663_);
                                if v___x_3727_ == 0 {
                                    v___y_3718_ = v___x_3726_;
                                    state = 10;
                                    continue;
                                } else {
                                    v___x_3728_ = lean_nat_dec_le(v___x_3663_, v___x_3663_);
                                    if v___x_3728_ == 0 {
                                        if v___x_3727_ == 0 {
                                            v___y_3718_ = v___x_3726_;
                                            state = 10;
                                            continue;
                                        } else {
                                            v___x_3729_ = 0usize;
                                            v___x_3730_ = lean_usize_of_nat(v___x_3663_);
                                            v___x_3731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__17(v_snd_3679_, v_fst_3653_, v___x_3729_, v___x_3730_, v___x_3726_);
                                            v___y_3718_ = v___x_3731_;
                                            state = 10;
                                            continue;
                                        }
                                    } else {
                                        v___x_3732_ = 0usize;
                                        v___x_3733_ = lean_usize_of_nat(v___x_3663_);
                                        v___x_3734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__17(v_snd_3679_, v_fst_3653_, v___x_3732_, v___x_3733_, v___x_3726_);
                                        v___y_3718_ = v___x_3734_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                v_defects_3681_ = v_snd_3658_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_defects_3681_ = v_snd_3658_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3660_);
                        leanh::lean_dec(v_snd_3658_);
                        leanh::lean_dec(v_fst_3657_);
                        leanh::lean_del_object(v___x_3655_);
                        leanh::lean_dec(v_fst_3653_);
                        v_a_3735_ = leanh::lean_ctor_get(v___x_3665_, 0);
                        v_isSharedCheck_3742_ =
                            (!leanh::lean_is_exclusive(v___x_3665_)) as u8;
                        if v_isSharedCheck_3742_ == 0 {
                            v___x_3737_ = v___x_3665_;
                            v_isShared_3738_ = v_isSharedCheck_3742_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3735_);
                            leanh::lean_dec(v___x_3665_);
                            v___x_3737_ = leanh::lean_box(0);
                            v_isShared_3738_ = v_isSharedCheck_3742_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    if v_isShared_3661_ == 0 {
                        v___x_3744_ = v___x_3660_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3749_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_fst_3657_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_snd_3658_);
                        v___x_3744_ = v_reuseFailAlloc_3749_;
                        state = 13;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3661_ == 0 {
                    leanh::lean_ctor_set(v___x_3660_, 1, v___y_3668_);
                    leanh::lean_ctor_set(v___x_3660_, 0, v___y_3669_);
                    v___x_3672_ = v___x_3660_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3677_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___y_3669_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3677_, 1, v___y_3668_);
                    v___x_3672_ = v_reuseFailAlloc_3677_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3656_ == 0 {
                    leanh::lean_ctor_set(v___x_3655_, 1, v___x_3672_);
                    leanh::lean_ctor_set(v___x_3655_, 0, v___y_3670_);
                    v___x_3674_ = v___x_3655_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3676_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___y_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3676_, 1, v___x_3672_);
                    v___x_3674_ = v_reuseFailAlloc_3676_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_3645_ = v___x_3674_;
                state = 0;
                continue;
            }
            6 => {
                leanh::lean_inc(v_snd_3679_);
                v___x_3682_ = lean_array_push(v_fst_3657_, v_snd_3679_);
                v_sz_3683_ = lean_array_size(v_fst_3653_);
                v___x_3684_ = 0usize;
                v___x_3685_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10(v_snd_3679_, v_sz_3683_, v___x_3684_, v_fst_3653_);
                leanh::lean_dec(v_snd_3679_);
                v___x_3686_ = lean_array_get_size(v___x_3685_);
                v___x_3687_ = l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg___closed__0;
                v___x_3688_ = lean_nat_dec_lt(v___x_3662_, v___x_3686_);
                if v___x_3688_ == 0 {
                    leanh::lean_dec_ref(v___x_3685_);
                    v___y_3668_ = v_defects_3681_;
                    v___y_3669_ = v___x_3682_;
                    v___y_3670_ = v___x_3687_;
                    state = 3;
                    continue;
                } else {
                    v___x_3689_ = lean_nat_dec_le(v___x_3686_, v___x_3686_);
                    if v___x_3689_ == 0 {
                        if v___x_3688_ == 0 {
                            leanh::lean_dec_ref(v___x_3685_);
                            v___y_3668_ = v_defects_3681_;
                            v___y_3669_ = v___x_3682_;
                            v___y_3670_ = v___x_3687_;
                            state = 3;
                            continue;
                        } else {
                            v___x_3690_ = lean_usize_of_nat(v___x_3686_);
                            v___x_3691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11(v___x_3685_, v___x_3684_, v___x_3690_, v___x_3687_);
                            leanh::lean_dec_ref(v___x_3685_);
                            v___y_3668_ = v_defects_3681_;
                            v___y_3669_ = v___x_3682_;
                            v___y_3670_ = v___x_3691_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3692_ = lean_usize_of_nat(v___x_3686_);
                        v___x_3693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11(v___x_3685_, v___x_3684_, v___x_3692_, v___x_3687_);
                        leanh::lean_dec_ref(v___x_3685_);
                        v___y_3668_ = v_defects_3681_;
                        v___y_3669_ = v___x_3682_;
                        v___y_3670_ = v___x_3693_;
                        state = 3;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3696_ = l_Array_eraseReps___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__13(v___y_3695_);
                leanh::lean_dec_ref(v___y_3695_);
                v___x_3697_ = l_Array_contains___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__12(v_parentNames_3644_, v_snd_3679_);
                v_sz_3698_ = lean_array_size(v___x_3696_);
                v___x_3699_ = 0usize;
                v___x_3700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__14(v_parentNames_3644_, v_sz_3698_, v___x_3699_, v___x_3696_);
                leanh::lean_inc(v_snd_3679_);
                v___x_3701_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3701_, 0, v_snd_3679_);
                leanh::lean_ctor_set(v___x_3701_, 1, v___x_3700_);
                leanh::lean_ctor_set_uint8(
                    v___x_3701_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3697_,
                );
                v___x_3702_ = lean_array_push(v_snd_3658_, v___x_3701_);
                v_defects_3681_ = v___x_3702_;
                state = 6;
                continue;
            }
            8 => {
                v___x_3708_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16___redArg(v___y_3705_, v___y_3706_, v___y_3704_, v___y_3707_);
                leanh::lean_dec(v___y_3707_);
                leanh::lean_dec(v___y_3705_);
                v___y_3695_ = v___x_3708_;
                state = 7;
                continue;
            }
            9 => {
                v___x_3714_ = lean_nat_dec_le(v___y_3713_, v___y_3710_);
                if v___x_3714_ == 0 {
                    leanh::lean_dec(v___y_3710_);
                    leanh::lean_inc(v___y_3713_);
                    v___y_3704_ = v___y_3713_;
                    v___y_3705_ = v___y_3711_;
                    v___y_3706_ = v___y_3712_;
                    v___y_3707_ = v___y_3713_;
                    state = 8;
                    continue;
                } else {
                    v___y_3704_ = v___y_3713_;
                    v___y_3705_ = v___y_3711_;
                    v___y_3706_ = v___y_3712_;
                    v___y_3707_ = v___y_3710_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v_sz_3719_ = lean_array_size(v___y_3718_);
                v___x_3720_ = 0usize;
                v___x_3721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__15(v_sz_3719_, v___x_3720_, v___y_3718_);
                v___x_3722_ = lean_array_get_size(v___x_3721_);
                v___x_3723_ = lean_nat_dec_eq(v___x_3722_, v___x_3662_);
                if v___x_3723_ == 0 {
                    v___x_3724_ = lean_nat_sub(v___x_3722_, v___x_3716_);
                    v___x_3725_ = lean_nat_dec_le(v___x_3662_, v___x_3724_);
                    if v___x_3725_ == 0 {
                        leanh::lean_inc(v___x_3724_);
                        v___y_3710_ = v___x_3724_;
                        v___y_3711_ = v___x_3722_;
                        v___y_3712_ = v___x_3721_;
                        v___y_3713_ = v___x_3724_;
                        state = 9;
                        continue;
                    } else {
                        v___y_3710_ = v___x_3724_;
                        v___y_3711_ = v___x_3722_;
                        v___y_3712_ = v___x_3721_;
                        v___y_3713_ = v___x_3662_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___y_3695_ = v___x_3721_;
                    state = 7;
                    continue;
                }
            }
            11 => {
                if v_isShared_3738_ == 0 {
                    v___x_3740_ = v___x_3737_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3741_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
                    v___x_3740_ = v_reuseFailAlloc_3741_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3740_;
            }
            13 => {
                if v_isShared_3656_ == 0 {
                    leanh::lean_ctor_set(v___x_3655_, 1, v___x_3744_);
                    v___x_3746_ = v___x_3655_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3748_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_fst_3653_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3748_, 1, v___x_3744_);
                    v___x_3746_ = v_reuseFailAlloc_3748_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_3747_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3747_, 0, v___x_3746_);
                return v___x_3747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg___boxed(
    mut v_relaxed_3752_: *mut leanh::LeanObject,
    mut v_parentNames_3753_: *mut leanh::LeanObject,
    mut v_a_3754_: *mut leanh::LeanObject,
    mut v___y_3755_: *mut leanh::LeanObject,
    mut v___y_3756_: *mut leanh::LeanObject,
    mut v___y_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
    mut v___y_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_relaxed_boxed_3761_: u8 = 0;
    let mut v_res_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_3761_ = (leanh::lean_unbox(v_relaxed_3752_) as u8);
    v_res_3762_ = l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg(v_relaxed_boxed_3761_, v_parentNames_3753_, v_a_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
    leanh::lean_dec(v___y_3759_);
    leanh::lean_dec_ref(v___y_3758_);
    leanh::lean_dec(v___y_3757_);
    leanh::lean_dec_ref(v___y_3756_);
    leanh::lean_dec(v___y_3755_);
    leanh::lean_dec_ref(v_parentNames_3753_);
    return v_res_3762_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4(
    mut v_structName_3765_: *mut leanh::LeanObject,
    mut v_parentNames_3766_: *mut leanh::LeanObject,
    mut v_relaxed_3767_: u8,
    mut v___y_3768_: *mut leanh::LeanObject,
    mut v___y_3769_: *mut leanh::LeanObject,
    mut v___y_3770_: *mut leanh::LeanObject,
    mut v___y_3771_: *mut leanh::LeanObject,
    mut v___y_3772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_3774_: usize = 0;
    let mut v___x_3775_: usize = 0;
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resOrder_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defects_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v_snd_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3804_: u8 = 0;
    let mut v_isSharedCheck_3805_: u8 = 0;
    let mut v_a_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3809_: u8 = 0;
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3813_: u8 = 0;
    let mut v_j_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: u8 = 0;
    let mut v___x_3820_: u8 = 0;
    let mut v___x_3821_: usize = 0;
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: usize = 0;
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3828_: u8 = 0;
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_3774_ = lean_array_size(v_parentNames_3766_);
                v___x_3775_ = 0usize;
                leanh::lean_inc_ref(v_parentNames_3766_);
                v___x_3776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__6(v_sz_3774_, v___x_3775_, v_parentNames_3766_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
                if leanh::lean_obj_tag(v___x_3776_) == 0 {
                    v_a_3777_ = leanh::lean_ctor_get(v___x_3776_, 0);
                    leanh::lean_inc(v_a_3777_);
                    leanh::lean_dec_ref_known(v___x_3776_, 1);
                    v___x_3778_ = leanh::lean_unsigned_to_nat(0);
                    v_j_3814_ = lean_array_get_size(v_a_3777_);
                    leanh::lean_inc_ref(v_parentNames_3766_);
                    v_as_3815_ = lean_array_push(v_a_3777_, v_parentNames_3766_);
                    v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                        leanh::lean_box(0),
                        v___x_3778_,
                        v_as_3815_,
                        v_j_3814_,
                    );
                    v___x_3817_ = lean_array_get_size(v___x_3816_);
                    v___x_3818_ = l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg___closed__0;
                    v___x_3819_ = lean_nat_dec_lt(v___x_3778_, v___x_3817_);
                    if v___x_3819_ == 0 {
                        leanh::lean_dec_ref(v___x_3816_);
                        v___y_3780_ = v___x_3818_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3820_ = lean_nat_dec_le(v___x_3817_, v___x_3817_);
                        if v___x_3820_ == 0 {
                            if v___x_3819_ == 0 {
                                leanh::lean_dec_ref(v___x_3816_);
                                v___y_3780_ = v___x_3818_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3821_ = lean_usize_of_nat(v___x_3817_);
                                v___x_3822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11(v___x_3816_, v___x_3775_, v___x_3821_, v___x_3818_);
                                leanh::lean_dec_ref(v___x_3816_);
                                v___y_3780_ = v___x_3822_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_3823_ = lean_usize_of_nat(v___x_3817_);
                            v___x_3824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__11(v___x_3816_, v___x_3775_, v___x_3823_, v___x_3818_);
                            leanh::lean_dec_ref(v___x_3816_);
                            v___y_3780_ = v___x_3824_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_parentNames_3766_);
                    leanh::lean_dec(v_structName_3765_);
                    v_a_3825_ = leanh::lean_ctor_get(v___x_3776_, 0);
                    v_isSharedCheck_3832_ = (!leanh::lean_is_exclusive(v___x_3776_)) as u8;
                    if v_isSharedCheck_3832_ == 0 {
                        v___x_3827_ = v___x_3776_;
                        v_isShared_3828_ = v_isSharedCheck_3832_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3825_);
                        leanh::lean_dec(v___x_3776_);
                        v___x_3827_ = leanh::lean_box(0);
                        v_isShared_3828_ = v_isSharedCheck_3832_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3781_ = leanh::lean_unsigned_to_nat(1);
                v___x_3782_ = lean_mk_empty_array_with_capacity(v___x_3781_);
                v_resOrder_3783_ = lean_array_push(v___x_3782_, v_structName_3765_);
                v_defects_3784_ = l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1___closed__0;
                v___x_3785_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3785_, 0, v_resOrder_3783_);
                leanh::lean_ctor_set(v___x_3785_, 1, v_defects_3784_);
                v___x_3786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3786_, 0, v___y_3780_);
                leanh::lean_ctor_set(v___x_3786_, 1, v___x_3785_);
                v___x_3787_ = l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg(v_relaxed_3767_, v_parentNames_3766_, v___x_3786_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
                leanh::lean_dec_ref(v_parentNames_3766_);
                if leanh::lean_obj_tag(v___x_3787_) == 0 {
                    v_a_3788_ = leanh::lean_ctor_get(v___x_3787_, 0);
                    v_isSharedCheck_3805_ = (!leanh::lean_is_exclusive(v___x_3787_)) as u8;
                    if v_isSharedCheck_3805_ == 0 {
                        v___x_3790_ = v___x_3787_;
                        v_isShared_3791_ = v_isSharedCheck_3805_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3788_);
                        leanh::lean_dec(v___x_3787_);
                        v___x_3790_ = leanh::lean_box(0);
                        v_isShared_3791_ = v_isSharedCheck_3805_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3806_ = leanh::lean_ctor_get(v___x_3787_, 0);
                    v_isSharedCheck_3813_ = (!leanh::lean_is_exclusive(v___x_3787_)) as u8;
                    if v_isSharedCheck_3813_ == 0 {
                        v___x_3808_ = v___x_3787_;
                        v_isShared_3809_ = v_isSharedCheck_3813_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3806_);
                        leanh::lean_dec(v___x_3787_);
                        v___x_3808_ = leanh::lean_box(0);
                        v_isShared_3809_ = v_isSharedCheck_3813_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_3792_ = leanh::lean_ctor_get(v_a_3788_, 1);
                leanh::lean_inc(v_snd_3792_);
                leanh::lean_dec(v_a_3788_);
                v_fst_3793_ = leanh::lean_ctor_get(v_snd_3792_, 0);
                v_snd_3794_ = leanh::lean_ctor_get(v_snd_3792_, 1);
                v_isSharedCheck_3804_ = (!leanh::lean_is_exclusive(v_snd_3792_)) as u8;
                if v_isSharedCheck_3804_ == 0 {
                    v___x_3796_ = v_snd_3792_;
                    v_isShared_3797_ = v_isSharedCheck_3804_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3794_);
                    leanh::lean_inc(v_fst_3793_);
                    leanh::lean_dec(v_snd_3792_);
                    v___x_3796_ = leanh::lean_box(0);
                    v_isShared_3797_ = v_isSharedCheck_3804_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3797_ == 0 {
                    v___x_3799_ = v___x_3796_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3803_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_fst_3793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3803_, 1, v_snd_3794_);
                    v___x_3799_ = v_reuseFailAlloc_3803_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3791_ == 0 {
                    leanh::lean_ctor_set(v___x_3790_, 0, v___x_3799_);
                    v___x_3801_ = v___x_3790_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3802_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3799_);
                    v___x_3801_ = v_reuseFailAlloc_3802_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3801_;
            }
            6 => {
                if v_isShared_3809_ == 0 {
                    v___x_3811_ = v___x_3808_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3812_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
                    v___x_3811_ = v_reuseFailAlloc_3812_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3811_;
            }
            8 => {
                if v_isShared_3828_ == 0 {
                    v___x_3830_ = v___x_3827_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3831_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
                    v___x_3830_ = v_reuseFailAlloc_3831_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1(
    mut v_structName_3833_: *mut leanh::LeanObject,
    mut v_relaxed_3834_: u8,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
    mut v___y_3837_: *mut leanh::LeanObject,
    mut v___y_3838_: *mut leanh::LeanObject,
    mut v___y_3839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3853_: u8 = 0;
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3855_: usize = 0;
    let mut v___x_3856_: usize = 0;
    let mut v_parentNames_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resolutionOrder_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3864_: u8 = 0;
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3868_: u8 = 0;
    let mut v_unused_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3873_: u8 = 0;
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3841_ = lean_st_ref_get(v___y_3839_);
                v_env_3842_ = leanh::lean_ctor_get(v___x_3841_, 0);
                leanh::lean_inc_ref_n(v_env_3842_, 2);
                leanh::lean_dec(v___x_3841_);
                v___x_3843_ = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(
                    v_env_3842_,
                    v_structName_3833_,
                );
                if leanh::lean_obj_tag(v___x_3843_) == 1 {
                    leanh::lean_dec_ref(v_env_3842_);
                    leanh::lean_dec(v_structName_3833_);
                    v_val_3844_ = leanh::lean_ctor_get(v___x_3843_, 0);
                    v_isSharedCheck_3853_ = (!leanh::lean_is_exclusive(v___x_3843_)) as u8;
                    if v_isSharedCheck_3853_ == 0 {
                        v___x_3846_ = v___x_3843_;
                        v_isShared_3847_ = v_isSharedCheck_3853_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3844_);
                        leanh::lean_dec(v___x_3843_);
                        v___x_3846_ = leanh::lean_box(0);
                        v_isShared_3847_ = v_isSharedCheck_3853_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3843_);
                    leanh::lean_inc_n(v_structName_3833_, 2);
                    v___x_3854_ = l_Lean_getStructureParentInfo(v_env_3842_, v_structName_3833_);
                    v_sz_3855_ = lean_array_size(v___x_3854_);
                    v___x_3856_ = 0usize;
                    v_parentNames_3857_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__3(v_sz_3855_, v___x_3856_, v___x_3854_);
                    v___x_3858_ = l_Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4(v_structName_3833_, v_parentNames_3857_, v_relaxed_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
                    if leanh::lean_obj_tag(v___x_3858_) == 0 {
                        v_a_3859_ = leanh::lean_ctor_get(v___x_3858_, 0);
                        leanh::lean_inc(v_a_3859_);
                        leanh::lean_dec_ref_known(v___x_3858_, 1);
                        v_resolutionOrder_3860_ = leanh::lean_ctor_get(v_a_3859_, 0);
                        leanh::lean_inc_ref(v_resolutionOrder_3860_);
                        v___x_3861_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg(v_structName_3833_, v_resolutionOrder_3860_, v___y_3837_, v___y_3839_);
                        if leanh::lean_obj_tag(v___x_3861_) == 0 {
                            v_isSharedCheck_3868_ =
                                (!leanh::lean_is_exclusive(v___x_3861_)) as u8;
                            if v_isSharedCheck_3868_ == 0 {
                                v_unused_3869_ = leanh::lean_ctor_get(v___x_3861_, 0);
                                leanh::lean_dec(v_unused_3869_);
                                v___x_3863_ = v___x_3861_;
                                v_isShared_3864_ = v_isSharedCheck_3868_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3861_);
                                v___x_3863_ = leanh::lean_box(0);
                                v_isShared_3864_ = v_isSharedCheck_3868_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3859_);
                            v_a_3870_ = leanh::lean_ctor_get(v___x_3861_, 0);
                            v_isSharedCheck_3877_ =
                                (!leanh::lean_is_exclusive(v___x_3861_)) as u8;
                            if v_isSharedCheck_3877_ == 0 {
                                v___x_3872_ = v___x_3861_;
                                v_isShared_3873_ = v_isSharedCheck_3877_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3870_);
                                leanh::lean_dec(v___x_3861_);
                                v___x_3872_ = leanh::lean_box(0);
                                v_isShared_3873_ = v_isSharedCheck_3877_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_structName_3833_);
                        return v___x_3858_;
                    }
                }
            }
            1 => {
                v___x_3848_ = l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1___closed__0;
                v___x_3849_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3849_, 0, v_val_3844_);
                leanh::lean_ctor_set(v___x_3849_, 1, v___x_3848_);
                if v_isShared_3847_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3846_, 0);
                    leanh::lean_ctor_set(v___x_3846_, 0, v___x_3849_);
                    v___x_3851_ = v___x_3846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3852_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3852_, 0, v___x_3849_);
                    v___x_3851_ = v_reuseFailAlloc_3852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3851_;
            }
            3 => {
                if v_isShared_3864_ == 0 {
                    leanh::lean_ctor_set(v___x_3863_, 0, v_a_3859_);
                    v___x_3866_ = v___x_3863_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3867_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3859_);
                    v___x_3866_ = v_reuseFailAlloc_3867_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3866_;
            }
            5 => {
                if v_isShared_3873_ == 0 {
                    v___x_3875_ = v___x_3872_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3876_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
                    v___x_3875_ = v_reuseFailAlloc_3876_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_sz_3878_: usize,
    mut v_i_3879_: usize,
    mut v_bs_3880_: *mut leanh::LeanObject,
    mut v___y_3881_: *mut leanh::LeanObject,
    mut v___y_3882_: *mut leanh::LeanObject,
    mut v___y_3883_: *mut leanh::LeanObject,
    mut v___y_3884_: *mut leanh::LeanObject,
    mut v___y_3885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3887_: u8 = 0;
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resolutionOrder_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: usize = 0;
    let mut v___x_3896_: usize = 0;
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3887_ = lean_usize_dec_lt(v_i_3879_, v_sz_3878_);
                if v___x_3887_ == 0 {
                    v___x_3888_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3888_, 0, v_bs_3880_);
                    return v___x_3888_;
                } else {
                    v_v_3889_ = lean_array_uget_borrowed(v_bs_3880_, v_i_3879_);
                    leanh::lean_inc(v_v_3889_);
                    v___x_3890_ = l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1(v_v_3889_, v___x_3887_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
                    if leanh::lean_obj_tag(v___x_3890_) == 0 {
                        v_a_3891_ = leanh::lean_ctor_get(v___x_3890_, 0);
                        leanh::lean_inc(v_a_3891_);
                        leanh::lean_dec_ref_known(v___x_3890_, 1);
                        v_resolutionOrder_3892_ = leanh::lean_ctor_get(v_a_3891_, 0);
                        leanh::lean_inc_ref(v_resolutionOrder_3892_);
                        leanh::lean_dec(v_a_3891_);
                        v___x_3893_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3894_ = lean_array_uset(v_bs_3880_, v_i_3879_, v___x_3893_);
                        v___x_3895_ = 1usize;
                        v___x_3896_ = lean_usize_add(v_i_3879_, v___x_3895_);
                        v___x_3897_ =
                            lean_array_uset(v_bs_x27_3894_, v_i_3879_, v_resolutionOrder_3892_);
                        v_i_3879_ = v___x_3896_;
                        v_bs_3880_ = v___x_3897_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_3880_);
                        v_a_3899_ = leanh::lean_ctor_get(v___x_3890_, 0);
                        v_isSharedCheck_3906_ =
                            (!leanh::lean_is_exclusive(v___x_3890_)) as u8;
                        if v_isSharedCheck_3906_ == 0 {
                            v___x_3901_ = v___x_3890_;
                            v_isShared_3902_ = v_isSharedCheck_3906_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3899_);
                            leanh::lean_dec(v___x_3890_);
                            v___x_3901_ = leanh::lean_box(0);
                            v_isShared_3902_ = v_isSharedCheck_3906_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3902_ == 0 {
                    v___x_3904_ = v___x_3901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
                    v___x_3904_ = v_reuseFailAlloc_3905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3904_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_sz_3907_: *mut leanh::LeanObject,
    mut v_i_3908_: *mut leanh::LeanObject,
    mut v_bs_3909_: *mut leanh::LeanObject,
    mut v___y_3910_: *mut leanh::LeanObject,
    mut v___y_3911_: *mut leanh::LeanObject,
    mut v___y_3912_: *mut leanh::LeanObject,
    mut v___y_3913_: *mut leanh::LeanObject,
    mut v___y_3914_: *mut leanh::LeanObject,
    mut v___y_3915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3916_: usize = 0;
    let mut v_i_boxed_3917_: usize = 0;
    let mut v_res_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3916_ = leanh::lean_unbox_usize(v_sz_3907_);
    leanh::lean_dec(v_sz_3907_);
    v_i_boxed_3917_ = leanh::lean_unbox_usize(v_i_3908_);
    leanh::lean_dec(v_i_3908_);
    v_res_3918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__6(v_sz_boxed_3916_, v_i_boxed_3917_, v_bs_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
    leanh::lean_dec(v___y_3914_);
    leanh::lean_dec_ref(v___y_3913_);
    leanh::lean_dec(v___y_3912_);
    leanh::lean_dec_ref(v___y_3911_);
    leanh::lean_dec(v___y_3910_);
    return v_res_3918_;
}
pub unsafe fn l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1___boxed(
    mut v_structName_3919_: *mut leanh::LeanObject,
    mut v_relaxed_3920_: *mut leanh::LeanObject,
    mut v___y_3921_: *mut leanh::LeanObject,
    mut v___y_3922_: *mut leanh::LeanObject,
    mut v___y_3923_: *mut leanh::LeanObject,
    mut v___y_3924_: *mut leanh::LeanObject,
    mut v___y_3925_: *mut leanh::LeanObject,
    mut v___y_3926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_relaxed_boxed_3927_: u8 = 0;
    let mut v_res_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_3927_ = (leanh::lean_unbox(v_relaxed_3920_) as u8);
    v_res_3928_ = l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1(v_structName_3919_, v_relaxed_boxed_3927_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
    leanh::lean_dec(v___y_3925_);
    leanh::lean_dec_ref(v___y_3924_);
    leanh::lean_dec(v___y_3923_);
    leanh::lean_dec_ref(v___y_3922_);
    leanh::lean_dec(v___y_3921_);
    return v_res_3928_;
}
pub unsafe fn l_Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_structName_3929_: *mut leanh::LeanObject,
    mut v_parentNames_3930_: *mut leanh::LeanObject,
    mut v_relaxed_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
    mut v___y_3935_: *mut leanh::LeanObject,
    mut v___y_3936_: *mut leanh::LeanObject,
    mut v___y_3937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_relaxed_boxed_3938_: u8 = 0;
    let mut v_res_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_3938_ = (leanh::lean_unbox(v_relaxed_3931_) as u8);
    v_res_3939_ = l_Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4(v_structName_3929_, v_parentNames_3930_, v_relaxed_boxed_3938_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
    leanh::lean_dec(v___y_3936_);
    leanh::lean_dec_ref(v___y_3935_);
    leanh::lean_dec(v___y_3934_);
    leanh::lean_dec_ref(v___y_3933_);
    leanh::lean_dec(v___y_3932_);
    return v_res_3939_;
}
pub unsafe fn l_Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0(
    mut v_structName_3940_: *mut leanh::LeanObject,
    mut v___y_3941_: *mut leanh::LeanObject,
    mut v___y_3942_: *mut leanh::LeanObject,
    mut v___y_3943_: *mut leanh::LeanObject,
    mut v___y_3944_: *mut leanh::LeanObject,
    mut v___y_3945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3947_: u8 = 0;
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3952_: u8 = 0;
    let mut v_resolutionOrder_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3957_: u8 = 0;
    let mut v_a_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3961_: u8 = 0;
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3965_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3947_ = 1;
                v___x_3948_ = l_Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1(v_structName_3940_, v___x_3947_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
                if leanh::lean_obj_tag(v___x_3948_) == 0 {
                    v_a_3949_ = leanh::lean_ctor_get(v___x_3948_, 0);
                    v_isSharedCheck_3957_ = (!leanh::lean_is_exclusive(v___x_3948_)) as u8;
                    if v_isSharedCheck_3957_ == 0 {
                        v___x_3951_ = v___x_3948_;
                        v_isShared_3952_ = v_isSharedCheck_3957_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3949_);
                        leanh::lean_dec(v___x_3948_);
                        v___x_3951_ = leanh::lean_box(0);
                        v_isShared_3952_ = v_isSharedCheck_3957_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3958_ = leanh::lean_ctor_get(v___x_3948_, 0);
                    v_isSharedCheck_3965_ = (!leanh::lean_is_exclusive(v___x_3948_)) as u8;
                    if v_isSharedCheck_3965_ == 0 {
                        v___x_3960_ = v___x_3948_;
                        v_isShared_3961_ = v_isSharedCheck_3965_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3958_);
                        leanh::lean_dec(v___x_3948_);
                        v___x_3960_ = leanh::lean_box(0);
                        v_isShared_3961_ = v_isSharedCheck_3965_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_resolutionOrder_3953_ = leanh::lean_ctor_get(v_a_3949_, 0);
                leanh::lean_inc_ref(v_resolutionOrder_3953_);
                leanh::lean_dec(v_a_3949_);
                if v_isShared_3952_ == 0 {
                    leanh::lean_ctor_set(v___x_3951_, 0, v_resolutionOrder_3953_);
                    v___x_3955_ = v___x_3951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3956_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_resolutionOrder_3953_);
                    v___x_3955_ = v_reuseFailAlloc_3956_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3955_;
            }
            3 => {
                if v_isShared_3961_ == 0 {
                    v___x_3963_ = v___x_3960_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3964_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
                    v___x_3963_ = v_reuseFailAlloc_3964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3963_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0___boxed(
    mut v_structName_3966_: *mut leanh::LeanObject,
    mut v___y_3967_: *mut leanh::LeanObject,
    mut v___y_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
    mut v___y_3971_: *mut leanh::LeanObject,
    mut v___y_3972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3973_ = l_Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0(v_structName_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
    leanh::lean_dec(v___y_3971_);
    leanh::lean_dec_ref(v___y_3970_);
    leanh::lean_dec(v___y_3969_);
    leanh::lean_dec_ref(v___y_3968_);
    leanh::lean_dec(v___y_3967_);
    return v_res_3973_;
}
pub unsafe fn l_Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0(
    mut v_structName_3974_: *mut leanh::LeanObject,
    mut v___y_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3985_: u8 = 0;
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_structName_3974_);
                v___x_3981_ = l_Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0(v_structName_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
                if leanh::lean_obj_tag(v___x_3981_) == 0 {
                    v_a_3982_ = leanh::lean_ctor_get(v___x_3981_, 0);
                    v_isSharedCheck_3990_ = (!leanh::lean_is_exclusive(v___x_3981_)) as u8;
                    if v_isSharedCheck_3990_ == 0 {
                        v___x_3984_ = v___x_3981_;
                        v_isShared_3985_ = v_isSharedCheck_3990_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3982_);
                        leanh::lean_dec(v___x_3981_);
                        v___x_3984_ = leanh::lean_box(0);
                        v_isShared_3985_ = v_isSharedCheck_3990_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_structName_3974_);
                    return v___x_3981_;
                }
            }
            1 => {
                v___x_3986_ = l_Array_erase___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__1(v_a_3982_, v_structName_3974_);
                leanh::lean_dec(v_structName_3974_);
                if v_isShared_3985_ == 0 {
                    leanh::lean_ctor_set(v___x_3984_, 0, v___x_3986_);
                    v___x_3988_ = v___x_3984_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3989_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3986_);
                    v___x_3988_ = v_reuseFailAlloc_3989_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0___boxed(
    mut v_structName_3991_: *mut leanh::LeanObject,
    mut v___y_3992_: *mut leanh::LeanObject,
    mut v___y_3993_: *mut leanh::LeanObject,
    mut v___y_3994_: *mut leanh::LeanObject,
    mut v___y_3995_: *mut leanh::LeanObject,
    mut v___y_3996_: *mut leanh::LeanObject,
    mut v___y_3997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3998_ = l_Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0(v_structName_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
    leanh::lean_dec(v___y_3996_);
    leanh::lean_dec_ref(v___y_3995_);
    leanh::lean_dec(v___y_3994_);
    leanh::lean_dec_ref(v___y_3993_);
    leanh::lean_dec(v___y_3992_);
    return v_res_3998_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__1___redArg(
    mut v_as_3999_: *mut leanh::LeanObject,
    mut v_sz_4000_: usize,
    mut v_i_4001_: usize,
    mut v_b_4002_: *mut leanh::LeanObject,
    mut v___y_4003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4005_: u8 = 0;
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: usize = 0;
    let mut v___x_4013_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4005_ = lean_usize_dec_lt(v_i_4001_, v_sz_4000_);
                if v___x_4005_ == 0 {
                    v___x_4006_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4006_, 0, v_b_4002_);
                    return v___x_4006_;
                } else {
                    v___x_4007_ = lean_st_ref_take(v___y_4003_);
                    v_a_4008_ = lean_array_uget_borrowed(v_as_3999_, v_i_4001_);
                    leanh::lean_inc(v_a_4008_);
                    v___x_4009_ = lean_array_push(v___x_4007_, v_a_4008_);
                    v___x_4010_ = lean_st_ref_set(v___y_4003_, v___x_4009_);
                    v___x_4011_ = leanh::lean_box(0);
                    v___x_4012_ = 1usize;
                    v___x_4013_ = lean_usize_add(v_i_4001_, v___x_4012_);
                    v_i_4001_ = v___x_4013_;
                    v_b_4002_ = v___x_4011_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__1___redArg___boxed(
    mut v_as_4015_: *mut leanh::LeanObject,
    mut v_sz_4016_: *mut leanh::LeanObject,
    mut v_i_4017_: *mut leanh::LeanObject,
    mut v_b_4018_: *mut leanh::LeanObject,
    mut v___y_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4021_: usize = 0;
    let mut v_i_boxed_4022_: usize = 0;
    let mut v_res_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4021_ = leanh::lean_unbox_usize(v_sz_4016_);
    leanh::lean_dec(v_sz_4016_);
    v_i_boxed_4022_ = leanh::lean_unbox_usize(v_i_4017_);
    leanh::lean_dec(v_i_4017_);
    v_res_4023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__1___redArg(v_as_4015_, v_sz_boxed_4021_, v_i_boxed_4022_, v_b_4018_, v___y_4019_);
    leanh::lean_dec(v___y_4019_);
    leanh::lean_dec_ref(v_as_4015_);
    return v_res_4023_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(
    mut v_type_4024_: *mut leanh::LeanObject,
    mut v_a_4025_: *mut leanh::LeanObject,
    mut v_a_4026_: *mut leanh::LeanObject,
    mut v_a_4027_: *mut leanh::LeanObject,
    mut v_a_4028_: *mut leanh::LeanObject,
    mut v_a_4029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v_val_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4048_: u8 = 0;
    let mut v_a_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4056_: u8 = 0;
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: u8 = 0;
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4068_: usize = 0;
    let mut v___x_4069_: usize = 0;
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4074_: u8 = 0;
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4078_: u8 = 0;
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4057_ = l_Lean_Expr_getAppFn(v_type_4024_);
                if leanh::lean_obj_tag(v___x_4057_) == 4 {
                    v_declName_4058_ = leanh::lean_ctor_get(v___x_4057_, 0);
                    leanh::lean_inc_n(v_declName_4058_, 3);
                    leanh::lean_dec_ref_known(v___x_4057_, 2);
                    v___x_4059_ = lean_st_ref_take(v_a_4025_);
                    v___x_4060_ = lean_array_push(v___x_4059_, v_declName_4058_);
                    v___x_4061_ = lean_st_ref_set(v_a_4025_, v___x_4060_);
                    v___x_4062_ = lean_st_ref_get(v_a_4029_);
                    v_env_4063_ = leanh::lean_ctor_get(v___x_4062_, 0);
                    leanh::lean_inc_ref(v_env_4063_);
                    leanh::lean_dec(v___x_4062_);
                    v___x_4064_ = l_Lean_isStructure(v_env_4063_, v_declName_4058_);
                    if v___x_4064_ == 0 {
                        leanh::lean_dec(v_declName_4058_);
                        v___y_4032_ = v_a_4025_;
                        v___y_4033_ = v_a_4026_;
                        v___y_4034_ = v_a_4027_;
                        v___y_4035_ = v_a_4028_;
                        v___y_4036_ = v_a_4029_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4065_ = l_Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0(v_declName_4058_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_);
                        if leanh::lean_obj_tag(v___x_4065_) == 0 {
                            v_a_4066_ = leanh::lean_ctor_get(v___x_4065_, 0);
                            leanh::lean_inc(v_a_4066_);
                            leanh::lean_dec_ref_known(v___x_4065_, 1);
                            v___x_4067_ = leanh::lean_box(0);
                            v_sz_4068_ = lean_array_size(v_a_4066_);
                            v___x_4069_ = 0usize;
                            v___x_4070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__1___redArg(v_a_4066_, v_sz_4068_, v___x_4069_, v___x_4067_, v_a_4025_);
                            leanh::lean_dec(v_a_4066_);
                            if leanh::lean_obj_tag(v___x_4070_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4070_, 1);
                                v___y_4032_ = v_a_4025_;
                                v___y_4033_ = v_a_4026_;
                                v___y_4034_ = v_a_4027_;
                                v___y_4035_ = v_a_4028_;
                                v___y_4036_ = v_a_4029_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_type_4024_);
                                return v___x_4070_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_type_4024_);
                            v_a_4071_ = leanh::lean_ctor_get(v___x_4065_, 0);
                            v_isSharedCheck_4078_ =
                                (!leanh::lean_is_exclusive(v___x_4065_)) as u8;
                            if v_isSharedCheck_4078_ == 0 {
                                v___x_4073_ = v___x_4065_;
                                v_isShared_4074_ = v_isSharedCheck_4078_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4071_);
                                leanh::lean_dec(v___x_4065_);
                                v___x_4073_ = leanh::lean_box(0);
                                v_isShared_4074_ = v_isSharedCheck_4078_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4057_);
                    leanh::lean_dec_ref(v_type_4024_);
                    v___x_4079_ = leanh::lean_box(0);
                    v___x_4080_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4080_, 0, v___x_4079_);
                    return v___x_4080_;
                }
            }
            1 => {
                v___x_4037_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(
                    v_type_4024_,
                    v___y_4033_,
                    v___y_4034_,
                    v___y_4035_,
                    v___y_4036_,
                );
                if leanh::lean_obj_tag(v___x_4037_) == 0 {
                    v_a_4038_ = leanh::lean_ctor_get(v___x_4037_, 0);
                    v_isSharedCheck_4048_ = (!leanh::lean_is_exclusive(v___x_4037_)) as u8;
                    if v_isSharedCheck_4048_ == 0 {
                        v___x_4040_ = v___x_4037_;
                        v_isShared_4041_ = v_isSharedCheck_4048_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4038_);
                        leanh::lean_dec(v___x_4037_);
                        v___x_4040_ = leanh::lean_box(0);
                        v_isShared_4041_ = v_isSharedCheck_4048_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4049_ = leanh::lean_ctor_get(v___x_4037_, 0);
                    v_isSharedCheck_4056_ = (!leanh::lean_is_exclusive(v___x_4037_)) as u8;
                    if v_isSharedCheck_4056_ == 0 {
                        v___x_4051_ = v___x_4037_;
                        v_isShared_4052_ = v_isSharedCheck_4056_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4049_);
                        leanh::lean_dec(v___x_4037_);
                        v___x_4051_ = leanh::lean_box(0);
                        v_isShared_4052_ = v_isSharedCheck_4056_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4038_) == 1 {
                    leanh::lean_del_object(v___x_4040_);
                    v_val_4042_ = leanh::lean_ctor_get(v_a_4038_, 0);
                    leanh::lean_inc(v_val_4042_);
                    leanh::lean_dec_ref_known(v_a_4038_, 1);
                    v_type_4024_ = v_val_4042_;
                    v_a_4025_ = v___y_4032_;
                    v_a_4026_ = v___y_4033_;
                    v_a_4027_ = v___y_4034_;
                    v_a_4028_ = v___y_4035_;
                    v_a_4029_ = v___y_4036_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_4038_);
                    v___x_4044_ = leanh::lean_box(0);
                    if v_isShared_4041_ == 0 {
                        leanh::lean_ctor_set(v___x_4040_, 0, v___x_4044_);
                        v___x_4046_ = v___x_4040_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4047_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4044_);
                        v___x_4046_ = v_reuseFailAlloc_4047_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4046_;
            }
            4 => {
                if v_isShared_4052_ == 0 {
                    v___x_4054_ = v___x_4051_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4055_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
                    v___x_4054_ = v_reuseFailAlloc_4055_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4054_;
            }
            6 => {
                if v_isShared_4074_ == 0 {
                    v___x_4076_ = v___x_4073_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4077_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
                    v___x_4076_ = v_reuseFailAlloc_4077_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4076_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___boxed(
    mut v_type_4081_: *mut leanh::LeanObject,
    mut v_a_4082_: *mut leanh::LeanObject,
    mut v_a_4083_: *mut leanh::LeanObject,
    mut v_a_4084_: *mut leanh::LeanObject,
    mut v_a_4085_: *mut leanh::LeanObject,
    mut v_a_4086_: *mut leanh::LeanObject,
    mut v_a_4087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4088_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(v_type_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_);
    leanh::lean_dec(v_a_4086_);
    leanh::lean_dec_ref(v_a_4085_);
    leanh::lean_dec(v_a_4084_);
    leanh::lean_dec_ref(v_a_4083_);
    leanh::lean_dec(v_a_4082_);
    return v_res_4088_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__1(
    mut v_as_4089_: *mut leanh::LeanObject,
    mut v_sz_4090_: usize,
    mut v_i_4091_: usize,
    mut v_b_4092_: *mut leanh::LeanObject,
    mut v___y_4093_: *mut leanh::LeanObject,
    mut v___y_4094_: *mut leanh::LeanObject,
    mut v___y_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__1___redArg(v_as_4089_, v_sz_4090_, v_i_4091_, v_b_4092_, v___y_4093_);
    return v___x_4099_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__1___boxed(
    mut v_as_4100_: *mut leanh::LeanObject,
    mut v_sz_4101_: *mut leanh::LeanObject,
    mut v_i_4102_: *mut leanh::LeanObject,
    mut v_b_4103_: *mut leanh::LeanObject,
    mut v___y_4104_: *mut leanh::LeanObject,
    mut v___y_4105_: *mut leanh::LeanObject,
    mut v___y_4106_: *mut leanh::LeanObject,
    mut v___y_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
    mut v___y_4109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4110_: usize = 0;
    let mut v_i_boxed_4111_: usize = 0;
    let mut v_res_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4110_ = leanh::lean_unbox_usize(v_sz_4101_);
    leanh::lean_dec(v_sz_4101_);
    v_i_boxed_4111_ = leanh::lean_unbox_usize(v_i_4102_);
    leanh::lean_dec(v_i_4102_);
    v_res_4112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__1(v_as_4100_, v_sz_boxed_4110_, v_i_boxed_4111_, v_b_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
    leanh::lean_dec(v___y_4108_);
    leanh::lean_dec_ref(v___y_4107_);
    leanh::lean_dec(v___y_4106_);
    leanh::lean_dec_ref(v___y_4105_);
    leanh::lean_dec(v___y_4104_);
    leanh::lean_dec_ref(v_as_4100_);
    return v_res_4112_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5(
    mut v_structName_4113_: *mut leanh::LeanObject,
    mut v_resolutionOrder_4114_: *mut leanh::LeanObject,
    mut v___y_4115_: *mut leanh::LeanObject,
    mut v___y_4116_: *mut leanh::LeanObject,
    mut v___y_4117_: *mut leanh::LeanObject,
    mut v___y_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4121_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___redArg(v_structName_4113_, v_resolutionOrder_4114_, v___y_4117_, v___y_4119_);
    return v___x_4121_;
}
pub unsafe fn l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_structName_4122_: *mut leanh::LeanObject,
    mut v_resolutionOrder_4123_: *mut leanh::LeanObject,
    mut v___y_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
    mut v___y_4127_: *mut leanh::LeanObject,
    mut v___y_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4130_ = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5(v_structName_4122_, v_resolutionOrder_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
    leanh::lean_dec(v___y_4128_);
    leanh::lean_dec_ref(v___y_4127_);
    leanh::lean_dec(v___y_4126_);
    leanh::lean_dec_ref(v___y_4125_);
    leanh::lean_dec(v___y_4124_);
    return v_res_4130_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16(
    mut v_n_4131_: *mut leanh::LeanObject,
    mut v_as_4132_: *mut leanh::LeanObject,
    mut v_lo_4133_: *mut leanh::LeanObject,
    mut v_hi_4134_: *mut leanh::LeanObject,
    mut v_w_4135_: *mut leanh::LeanObject,
    mut v_hlo_4136_: *mut leanh::LeanObject,
    mut v_hhi_4137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16___redArg(v_n_4131_, v_as_4132_, v_lo_4133_, v_hi_4134_);
    return v___x_4138_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16___boxed(
    mut v_n_4139_: *mut leanh::LeanObject,
    mut v_as_4140_: *mut leanh::LeanObject,
    mut v_lo_4141_: *mut leanh::LeanObject,
    mut v_hi_4142_: *mut leanh::LeanObject,
    mut v_w_4143_: *mut leanh::LeanObject,
    mut v_hlo_4144_: *mut leanh::LeanObject,
    mut v_hhi_4145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16(v_n_4139_, v_as_4140_, v_lo_4141_, v_hi_4142_, v_w_4143_, v_hlo_4144_, v_hhi_4145_);
    leanh::lean_dec(v_hi_4142_);
    leanh::lean_dec(v_n_4139_);
    return v_res_4146_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18(
    mut v_relaxed_4147_: u8,
    mut v_parentNames_4148_: *mut leanh::LeanObject,
    mut v_inst_4149_: *mut leanh::LeanObject,
    mut v_a_4150_: *mut leanh::LeanObject,
    mut v___y_4151_: *mut leanh::LeanObject,
    mut v___y_4152_: *mut leanh::LeanObject,
    mut v___y_4153_: *mut leanh::LeanObject,
    mut v___y_4154_: *mut leanh::LeanObject,
    mut v___y_4155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4157_ = l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___redArg(v_relaxed_4147_, v_parentNames_4148_, v_a_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
    return v___x_4157_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18___boxed(
    mut v_relaxed_4158_: *mut leanh::LeanObject,
    mut v_parentNames_4159_: *mut leanh::LeanObject,
    mut v_inst_4160_: *mut leanh::LeanObject,
    mut v_a_4161_: *mut leanh::LeanObject,
    mut v___y_4162_: *mut leanh::LeanObject,
    mut v___y_4163_: *mut leanh::LeanObject,
    mut v___y_4164_: *mut leanh::LeanObject,
    mut v___y_4165_: *mut leanh::LeanObject,
    mut v___y_4166_: *mut leanh::LeanObject,
    mut v___y_4167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_relaxed_boxed_4168_: u8 = 0;
    let mut v_res_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_relaxed_boxed_4168_ = (leanh::lean_unbox(v_relaxed_4158_) as u8);
    v_res_4169_ = l___private_Init_While_0__whileM_erased___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__18(v_relaxed_boxed_4168_, v_parentNames_4159_, v_inst_4160_, v_a_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
    leanh::lean_dec(v___y_4166_);
    leanh::lean_dec_ref(v___y_4165_);
    leanh::lean_dec(v___y_4164_);
    leanh::lean_dec_ref(v___y_4163_);
    leanh::lean_dec(v___y_4162_);
    leanh::lean_dec_ref(v_parentNames_4159_);
    return v_res_4169_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20(
    mut v_00_u03b2_4170_: *mut leanh::LeanObject,
    mut v_x_4171_: *mut leanh::LeanObject,
    mut v_x_4172_: *mut leanh::LeanObject,
    mut v_x_4173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4174_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20___redArg(v_x_4171_, v_x_4172_, v_x_4173_);
    return v___x_4174_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(
    mut v_upperBound_4175_: *mut leanh::LeanObject,
    mut v_resOrders_4176_: *mut leanh::LeanObject,
    mut v_next_4177_: *mut leanh::LeanObject,
    mut v___x_4178_: *mut leanh::LeanObject,
    mut v_inst_4179_: *mut leanh::LeanObject,
    mut v_R_4180_: *mut leanh::LeanObject,
    mut v_a_4181_: *mut leanh::LeanObject,
    mut v_b_4182_: *mut leanh::LeanObject,
    mut v_c_4183_: *mut leanh::LeanObject,
    mut v___y_4184_: *mut leanh::LeanObject,
    mut v___y_4185_: *mut leanh::LeanObject,
    mut v___y_4186_: *mut leanh::LeanObject,
    mut v___y_4187_: *mut leanh::LeanObject,
    mut v___y_4188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4190_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___redArg(v_upperBound_4175_, v_resOrders_4176_, v_next_4177_, v___x_4178_, v_a_4181_, v_b_4182_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
    return v___x_4190_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11___boxed(
    mut v_upperBound_4191_: *mut leanh::LeanObject,
    mut v_resOrders_4192_: *mut leanh::LeanObject,
    mut v_next_4193_: *mut leanh::LeanObject,
    mut v___x_4194_: *mut leanh::LeanObject,
    mut v_inst_4195_: *mut leanh::LeanObject,
    mut v_R_4196_: *mut leanh::LeanObject,
    mut v_a_4197_: *mut leanh::LeanObject,
    mut v_b_4198_: *mut leanh::LeanObject,
    mut v_c_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
    mut v___y_4202_: *mut leanh::LeanObject,
    mut v___y_4203_: *mut leanh::LeanObject,
    mut v___y_4204_: *mut leanh::LeanObject,
    mut v___y_4205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4206_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11(v_upperBound_4191_, v_resOrders_4192_, v_next_4193_, v___x_4194_, v_inst_4195_, v_R_4196_, v_a_4197_, v_b_4198_, v_c_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
    leanh::lean_dec(v___y_4204_);
    leanh::lean_dec_ref(v___y_4203_);
    leanh::lean_dec(v___y_4202_);
    leanh::lean_dec_ref(v___y_4201_);
    leanh::lean_dec(v___y_4200_);
    leanh::lean_dec(v_next_4193_);
    leanh::lean_dec(v_upperBound_4191_);
    return v_res_4206_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__12(
    mut v_upperBound_4207_: *mut leanh::LeanObject,
    mut v___x_4208_: *mut leanh::LeanObject,
    mut v_resOrders_4209_: *mut leanh::LeanObject,
    mut v_inst_4210_: *mut leanh::LeanObject,
    mut v_R_4211_: *mut leanh::LeanObject,
    mut v_a_4212_: *mut leanh::LeanObject,
    mut v_b_4213_: *mut leanh::LeanObject,
    mut v_c_4214_: *mut leanh::LeanObject,
    mut v___y_4215_: *mut leanh::LeanObject,
    mut v___y_4216_: *mut leanh::LeanObject,
    mut v___y_4217_: *mut leanh::LeanObject,
    mut v___y_4218_: *mut leanh::LeanObject,
    mut v___y_4219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__12___redArg(v_upperBound_4207_, v___x_4208_, v_resOrders_4209_, v_a_4212_, v_b_4213_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
    return v___x_4221_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__12___boxed(
    mut v_upperBound_4222_: *mut leanh::LeanObject,
    mut v___x_4223_: *mut leanh::LeanObject,
    mut v_resOrders_4224_: *mut leanh::LeanObject,
    mut v_inst_4225_: *mut leanh::LeanObject,
    mut v_R_4226_: *mut leanh::LeanObject,
    mut v_a_4227_: *mut leanh::LeanObject,
    mut v_b_4228_: *mut leanh::LeanObject,
    mut v_c_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
    mut v___y_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
    mut v___y_4234_: *mut leanh::LeanObject,
    mut v___y_4235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__12(v_upperBound_4222_, v___x_4223_, v_resOrders_4224_, v_inst_4225_, v_R_4226_, v_a_4227_, v_b_4228_, v_c_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_);
    leanh::lean_dec(v___y_4234_);
    leanh::lean_dec_ref(v___y_4233_);
    leanh::lean_dec(v___y_4232_);
    leanh::lean_dec_ref(v___y_4231_);
    leanh::lean_dec(v___y_4230_);
    leanh::lean_dec(v___x_4223_);
    leanh::lean_dec(v_upperBound_4222_);
    return v_res_4236_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16_spec__25(
    mut v_n_4237_: *mut leanh::LeanObject,
    mut v_lo_4238_: *mut leanh::LeanObject,
    mut v_hi_4239_: *mut leanh::LeanObject,
    mut v_hhi_4240_: *mut leanh::LeanObject,
    mut v_pivot_4241_: *mut leanh::LeanObject,
    mut v_as_4242_: *mut leanh::LeanObject,
    mut v_i_4243_: *mut leanh::LeanObject,
    mut v_k_4244_: *mut leanh::LeanObject,
    mut v_ilo_4245_: *mut leanh::LeanObject,
    mut v_ik_4246_: *mut leanh::LeanObject,
    mut v_w_4247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4248_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16_spec__25___redArg(v_hi_4239_, v_pivot_4241_, v_as_4242_, v_i_4243_, v_k_4244_);
    return v___x_4248_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16_spec__25___boxed(
    mut v_n_4249_: *mut leanh::LeanObject,
    mut v_lo_4250_: *mut leanh::LeanObject,
    mut v_hi_4251_: *mut leanh::LeanObject,
    mut v_hhi_4252_: *mut leanh::LeanObject,
    mut v_pivot_4253_: *mut leanh::LeanObject,
    mut v_as_4254_: *mut leanh::LeanObject,
    mut v_i_4255_: *mut leanh::LeanObject,
    mut v_k_4256_: *mut leanh::LeanObject,
    mut v_ilo_4257_: *mut leanh::LeanObject,
    mut v_ik_4258_: *mut leanh::LeanObject,
    mut v_w_4259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__16_spec__25(v_n_4249_, v_lo_4250_, v_hi_4251_, v_hhi_4252_, v_pivot_4253_, v_as_4254_, v_i_4255_, v_k_4256_, v_ilo_4257_, v_ik_4258_, v_w_4259_);
    leanh::lean_dec(v_pivot_4253_);
    leanh::lean_dec(v_hi_4251_);
    leanh::lean_dec(v_lo_4250_);
    leanh::lean_dec(v_n_4249_);
    return v_res_4260_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30(
    mut v_00_u03b2_4261_: *mut leanh::LeanObject,
    mut v_x_4262_: *mut leanh::LeanObject,
    mut v_x_4263_: usize,
    mut v_x_4264_: usize,
    mut v_x_4265_: *mut leanh::LeanObject,
    mut v_x_4266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___redArg(v_x_4262_, v_x_4263_, v_x_4264_, v_x_4265_, v_x_4266_);
    return v___x_4267_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30___boxed(
    mut v_00_u03b2_4268_: *mut leanh::LeanObject,
    mut v_x_4269_: *mut leanh::LeanObject,
    mut v_x_4270_: *mut leanh::LeanObject,
    mut v_x_4271_: *mut leanh::LeanObject,
    mut v_x_4272_: *mut leanh::LeanObject,
    mut v_x_4273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17464__boxed_4274_: usize = 0;
    let mut v_x_17465__boxed_4275_: usize = 0;
    let mut v_res_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17464__boxed_4274_ = leanh::lean_unbox_usize(v_x_4270_);
    leanh::lean_dec(v_x_4270_);
    v_x_17465__boxed_4275_ = leanh::lean_unbox_usize(v_x_4271_);
    leanh::lean_dec(v_x_4271_);
    v_res_4276_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30(v_00_u03b2_4268_, v_x_4269_, v_x_17464__boxed_4274_, v_x_17465__boxed_4275_, v_x_4272_, v_x_4273_);
    return v_res_4276_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16(
    mut v_upperBound_4277_: *mut leanh::LeanObject,
    mut v_resOrders_4278_: *mut leanh::LeanObject,
    mut v_next_4279_: *mut leanh::LeanObject,
    mut v___x_4280_: *mut leanh::LeanObject,
    mut v_inst_4281_: *mut leanh::LeanObject,
    mut v_R_4282_: *mut leanh::LeanObject,
    mut v_a_4283_: *mut leanh::LeanObject,
    mut v_b_4284_: *mut leanh::LeanObject,
    mut v_c_4285_: *mut leanh::LeanObject,
    mut v___y_4286_: *mut leanh::LeanObject,
    mut v___y_4287_: *mut leanh::LeanObject,
    mut v___y_4288_: *mut leanh::LeanObject,
    mut v___y_4289_: *mut leanh::LeanObject,
    mut v___y_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___redArg(v_upperBound_4277_, v_resOrders_4278_, v_next_4279_, v___x_4280_, v_a_4283_, v_b_4284_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
    return v___x_4292_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16___boxed(
    mut v_upperBound_4293_: *mut leanh::LeanObject,
    mut v_resOrders_4294_: *mut leanh::LeanObject,
    mut v_next_4295_: *mut leanh::LeanObject,
    mut v___x_4296_: *mut leanh::LeanObject,
    mut v_inst_4297_: *mut leanh::LeanObject,
    mut v_R_4298_: *mut leanh::LeanObject,
    mut v_a_4299_: *mut leanh::LeanObject,
    mut v_b_4300_: *mut leanh::LeanObject,
    mut v_c_4301_: *mut leanh::LeanObject,
    mut v___y_4302_: *mut leanh::LeanObject,
    mut v___y_4303_: *mut leanh::LeanObject,
    mut v___y_4304_: *mut leanh::LeanObject,
    mut v___y_4305_: *mut leanh::LeanObject,
    mut v___y_4306_: *mut leanh::LeanObject,
    mut v___y_4307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4308_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Lean_Structure_0__Lean_mergeStructureResolutionOrders_selectParent___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__7_spec__11_spec__16(v_upperBound_4293_, v_resOrders_4294_, v_next_4295_, v___x_4296_, v_inst_4297_, v_R_4298_, v_a_4299_, v_b_4300_, v_c_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
    leanh::lean_dec(v___y_4306_);
    leanh::lean_dec_ref(v___y_4305_);
    leanh::lean_dec(v___y_4304_);
    leanh::lean_dec_ref(v___y_4303_);
    leanh::lean_dec(v___y_4302_);
    leanh::lean_dec(v_next_4295_);
    leanh::lean_dec(v_upperBound_4293_);
    return v_res_4308_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__35(
    mut v_00_u03b2_4309_: *mut leanh::LeanObject,
    mut v_n_4310_: *mut leanh::LeanObject,
    mut v_k_4311_: *mut leanh::LeanObject,
    mut v_v_4312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4313_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__35___redArg(v_n_4310_, v_k_4311_, v_v_4312_);
    return v___x_4313_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36(
    mut v_00_u03b2_4314_: *mut leanh::LeanObject,
    mut v_depth_4315_: usize,
    mut v_keys_4316_: *mut leanh::LeanObject,
    mut v_vals_4317_: *mut leanh::LeanObject,
    mut v_heq_4318_: *mut leanh::LeanObject,
    mut v_i_4319_: *mut leanh::LeanObject,
    mut v_entries_4320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4321_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___redArg(v_depth_4315_, v_keys_4316_, v_vals_4317_, v_i_4319_, v_entries_4320_);
    return v___x_4321_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36___boxed(
    mut v_00_u03b2_4322_: *mut leanh::LeanObject,
    mut v_depth_4323_: *mut leanh::LeanObject,
    mut v_keys_4324_: *mut leanh::LeanObject,
    mut v_vals_4325_: *mut leanh::LeanObject,
    mut v_heq_4326_: *mut leanh::LeanObject,
    mut v_i_4327_: *mut leanh::LeanObject,
    mut v_entries_4328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4329_: usize = 0;
    let mut v_res_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4329_ = leanh::lean_unbox_usize(v_depth_4323_);
    leanh::lean_dec(v_depth_4323_);
    v_res_4330_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__36(v_00_u03b2_4322_, v_depth_boxed_4329_, v_keys_4324_, v_vals_4325_, v_heq_4326_, v_i_4327_, v_entries_4328_);
    leanh::lean_dec_ref(v_vals_4325_);
    leanh::lean_dec_ref(v_keys_4324_);
    return v_res_4330_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__35_spec__36(
    mut v_00_u03b2_4331_: *mut leanh::LeanObject,
    mut v_x_4332_: *mut leanh::LeanObject,
    mut v_x_4333_: *mut leanh::LeanObject,
    mut v_x_4334_: *mut leanh::LeanObject,
    mut v_x_4335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4336_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__5_spec__20_spec__30_spec__35_spec__36___redArg(v_x_4332_, v_x_4333_, v_x_4334_, v_x_4335_);
    return v___x_4336_;
}
pub unsafe fn l_Lean_Server_Completion_getDotCompletionTypeNames(
    mut v_type_4337_: *mut leanh::LeanObject,
    mut v_a_4338_: *mut leanh::LeanObject,
    mut v_a_4339_: *mut leanh::LeanObject,
    mut v_a_4340_: *mut leanh::LeanObject,
    mut v_a_4341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4348_: u8 = 0;
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4353_: u8 = 0;
    let mut v_unused_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10___closed__0;
                v___x_4344_ = lean_st_mk_ref(v___x_4343_);
                v___x_4345_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(v_type_4337_, v___x_4344_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
                if leanh::lean_obj_tag(v___x_4345_) == 0 {
                    v_isSharedCheck_4353_ = (!leanh::lean_is_exclusive(v___x_4345_)) as u8;
                    if v_isSharedCheck_4353_ == 0 {
                        v_unused_4354_ = leanh::lean_ctor_get(v___x_4345_, 0);
                        leanh::lean_dec(v_unused_4354_);
                        v___x_4347_ = v___x_4345_;
                        v_isShared_4348_ = v_isSharedCheck_4353_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4345_);
                        v___x_4347_ = leanh::lean_box(0);
                        v_isShared_4348_ = v_isSharedCheck_4353_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4344_);
                    v_a_4355_ = leanh::lean_ctor_get(v___x_4345_, 0);
                    v_isSharedCheck_4362_ = (!leanh::lean_is_exclusive(v___x_4345_)) as u8;
                    if v_isSharedCheck_4362_ == 0 {
                        v___x_4357_ = v___x_4345_;
                        v_isShared_4358_ = v_isSharedCheck_4362_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4355_);
                        leanh::lean_dec(v___x_4345_);
                        v___x_4357_ = leanh::lean_box(0);
                        v_isShared_4358_ = v_isSharedCheck_4362_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4349_ = lean_st_ref_get(v___x_4344_);
                leanh::lean_dec(v___x_4344_);
                if v_isShared_4348_ == 0 {
                    leanh::lean_ctor_set(v___x_4347_, 0, v___x_4349_);
                    v___x_4351_ = v___x_4347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4352_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4349_);
                    v___x_4351_ = v_reuseFailAlloc_4352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4351_;
            }
            3 => {
                if v_isShared_4358_ == 0 {
                    v___x_4360_ = v___x_4357_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4361_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
                    v___x_4360_ = v_reuseFailAlloc_4361_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Completion_getDotCompletionTypeNames___boxed(
    mut v_type_4363_: *mut leanh::LeanObject,
    mut v_a_4364_: *mut leanh::LeanObject,
    mut v_a_4365_: *mut leanh::LeanObject,
    mut v_a_4366_: *mut leanh::LeanObject,
    mut v_a_4367_: *mut leanh::LeanObject,
    mut v_a_4368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4369_ = l_Lean_Server_Completion_getDotCompletionTypeNames(
        v_type_4363_,
        v_a_4364_,
        v_a_4365_,
        v_a_4366_,
        v_a_4367_,
    );
    leanh::lean_dec(v_a_4367_);
    leanh::lean_dec_ref(v_a_4366_);
    leanh::lean_dec(v_a_4365_);
    leanh::lean_dec_ref(v_a_4364_);
    return v_res_4369_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__0___redArg(
    mut v_e_4370_: *mut leanh::LeanObject,
    mut v___y_4371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4393_: u8 = 0;
    let mut v_unused_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4373_ = l_Lean_Expr_hasMVar(v_e_4370_);
                if v___x_4373_ == 0 {
                    v___x_4374_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4374_, 0, v_e_4370_);
                    return v___x_4374_;
                } else {
                    v___x_4375_ = lean_st_ref_get(v___y_4371_);
                    v_mctx_4376_ = leanh::lean_ctor_get(v___x_4375_, 0);
                    leanh::lean_inc_ref(v_mctx_4376_);
                    leanh::lean_dec(v___x_4375_);
                    v___x_4377_ = l_Lean_instantiateMVarsCore(v_mctx_4376_, v_e_4370_);
                    v_fst_4378_ = leanh::lean_ctor_get(v___x_4377_, 0);
                    leanh::lean_inc(v_fst_4378_);
                    v_snd_4379_ = leanh::lean_ctor_get(v___x_4377_, 1);
                    leanh::lean_inc(v_snd_4379_);
                    leanh::lean_dec_ref(v___x_4377_);
                    v___x_4380_ = lean_st_ref_take(v___y_4371_);
                    v_cache_4381_ = leanh::lean_ctor_get(v___x_4380_, 1);
                    v_zetaDeltaFVarIds_4382_ = leanh::lean_ctor_get(v___x_4380_, 2);
                    v_postponed_4383_ = leanh::lean_ctor_get(v___x_4380_, 3);
                    v_diag_4384_ = leanh::lean_ctor_get(v___x_4380_, 4);
                    v_isSharedCheck_4393_ = (!leanh::lean_is_exclusive(v___x_4380_)) as u8;
                    if v_isSharedCheck_4393_ == 0 {
                        v_unused_4394_ = leanh::lean_ctor_get(v___x_4380_, 0);
                        leanh::lean_dec(v_unused_4394_);
                        v___x_4386_ = v___x_4380_;
                        v_isShared_4387_ = v_isSharedCheck_4393_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_4384_);
                        leanh::lean_inc(v_postponed_4383_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_4382_);
                        leanh::lean_inc(v_cache_4381_);
                        leanh::lean_dec(v___x_4380_);
                        v___x_4386_ = leanh::lean_box(0);
                        v_isShared_4387_ = v_isSharedCheck_4393_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4387_ == 0 {
                    leanh::lean_ctor_set(v___x_4386_, 0, v_snd_4379_);
                    v___x_4389_ = v___x_4386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4392_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_snd_4379_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4392_, 1, v_cache_4381_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4392_,
                        2,
                        v_zetaDeltaFVarIds_4382_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4392_, 3, v_postponed_4383_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4392_, 4, v_diag_4384_);
                    v___x_4389_ = v_reuseFailAlloc_4392_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4390_ = lean_st_ref_set(v___y_4371_, v___x_4389_);
                v___x_4391_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4391_, 0, v_fst_4378_);
                return v___x_4391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__0___redArg___boxed(
    mut v_e_4395_: *mut leanh::LeanObject,
    mut v___y_4396_: *mut leanh::LeanObject,
    mut v___y_4397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4398_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__0___redArg(v_e_4395_, v___y_4396_);
    leanh::lean_dec(v___y_4396_);
    return v_res_4398_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__0(
    mut v_e_4399_: *mut leanh::LeanObject,
    mut v___y_4400_: *mut leanh::LeanObject,
    mut v___y_4401_: *mut leanh::LeanObject,
    mut v___y_4402_: *mut leanh::LeanObject,
    mut v___y_4403_: *mut leanh::LeanObject,
    mut v___y_4404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4406_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__0___redArg(v_e_4399_, v___y_4402_);
    return v___x_4406_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__0___boxed(
    mut v_e_4407_: *mut leanh::LeanObject,
    mut v___y_4408_: *mut leanh::LeanObject,
    mut v___y_4409_: *mut leanh::LeanObject,
    mut v___y_4410_: *mut leanh::LeanObject,
    mut v___y_4411_: *mut leanh::LeanObject,
    mut v___y_4412_: *mut leanh::LeanObject,
    mut v___y_4413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4414_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__0(v_e_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
    leanh::lean_dec(v___y_4412_);
    leanh::lean_dec_ref(v___y_4411_);
    leanh::lean_dec(v___y_4410_);
    leanh::lean_dec_ref(v___y_4409_);
    leanh::lean_dec(v___y_4408_);
    return v_res_4414_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1___redArg___lam__0(
    mut v_k_4415_: *mut leanh::LeanObject,
    mut v___y_4416_: *mut leanh::LeanObject,
    mut v_b_4417_: *mut leanh::LeanObject,
    mut v_c_4418_: *mut leanh::LeanObject,
    mut v___y_4419_: *mut leanh::LeanObject,
    mut v___y_4420_: *mut leanh::LeanObject,
    mut v___y_4421_: *mut leanh::LeanObject,
    mut v___y_4422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4422_);
    leanh::lean_inc_ref(v___y_4421_);
    leanh::lean_inc(v___y_4420_);
    leanh::lean_inc_ref(v___y_4419_);
    leanh::lean_inc(v___y_4416_);
    v___x_4424_ = leanh::lean_apply_8(
        v_k_4415_,
        v_b_4417_,
        v_c_4418_,
        v___y_4416_,
        v___y_4419_,
        v___y_4420_,
        v___y_4421_,
        v___y_4422_,
        leanh::lean_box(0),
    );
    return v___x_4424_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1___redArg___lam__0___boxed(
    mut v_k_4425_: *mut leanh::LeanObject,
    mut v___y_4426_: *mut leanh::LeanObject,
    mut v_b_4427_: *mut leanh::LeanObject,
    mut v_c_4428_: *mut leanh::LeanObject,
    mut v___y_4429_: *mut leanh::LeanObject,
    mut v___y_4430_: *mut leanh::LeanObject,
    mut v___y_4431_: *mut leanh::LeanObject,
    mut v___y_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4434_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1___redArg___lam__0(v_k_4425_, v___y_4426_, v_b_4427_, v_c_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
    leanh::lean_dec(v___y_4432_);
    leanh::lean_dec_ref(v___y_4431_);
    leanh::lean_dec(v___y_4430_);
    leanh::lean_dec_ref(v___y_4429_);
    leanh::lean_dec(v___y_4426_);
    return v_res_4434_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1___redArg(
    mut v_type_4435_: *mut leanh::LeanObject,
    mut v_k_4436_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4437_: u8,
    mut v___y_4438_: *mut leanh::LeanObject,
    mut v___y_4439_: *mut leanh::LeanObject,
    mut v___y_4440_: *mut leanh::LeanObject,
    mut v___y_4441_: *mut leanh::LeanObject,
    mut v___y_4442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: u8 = 0;
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_4438_);
                v___f_4444_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                leanh::lean_closure_set(v___f_4444_, 0, v_k_4436_);
                leanh::lean_closure_set(v___f_4444_, 1, v___y_4438_);
                v___x_4445_ = 0;
                v___x_4446_ = leanh::lean_box(0);
                v___x_4447_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        leanh::lean_box(0),
                        v___x_4445_,
                        v___x_4446_,
                        v_type_4435_,
                        v___f_4444_,
                        v_cleanupAnnotations_4437_,
                        v___x_4445_,
                        v___y_4439_,
                        v___y_4440_,
                        v___y_4441_,
                        v___y_4442_,
                    );
                if leanh::lean_obj_tag(v___x_4447_) == 0 {
                    return v___x_4447_;
                } else {
                    v_a_4448_ = leanh::lean_ctor_get(v___x_4447_, 0);
                    v_isSharedCheck_4455_ = (!leanh::lean_is_exclusive(v___x_4447_)) as u8;
                    if v_isSharedCheck_4455_ == 0 {
                        v___x_4450_ = v___x_4447_;
                        v_isShared_4451_ = v_isSharedCheck_4455_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4448_);
                        leanh::lean_dec(v___x_4447_);
                        v___x_4450_ = leanh::lean_box(0);
                        v_isShared_4451_ = v_isSharedCheck_4455_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4451_ == 0 {
                    v___x_4453_ = v___x_4450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4454_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4454_, 0, v_a_4448_);
                    v___x_4453_ = v_reuseFailAlloc_4454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1___redArg___boxed(
    mut v_type_4456_: *mut leanh::LeanObject,
    mut v_k_4457_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4458_: *mut leanh::LeanObject,
    mut v___y_4459_: *mut leanh::LeanObject,
    mut v___y_4460_: *mut leanh::LeanObject,
    mut v___y_4461_: *mut leanh::LeanObject,
    mut v___y_4462_: *mut leanh::LeanObject,
    mut v___y_4463_: *mut leanh::LeanObject,
    mut v___y_4464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4465_: u8 = 0;
    let mut v_res_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4465_ = (leanh::lean_unbox(v_cleanupAnnotations_4458_) as u8);
    v_res_4466_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1___redArg(v_type_4456_, v_k_4457_, v_cleanupAnnotations_boxed_4465_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
    leanh::lean_dec(v___y_4463_);
    leanh::lean_dec_ref(v___y_4462_);
    leanh::lean_dec(v___y_4461_);
    leanh::lean_dec_ref(v___y_4460_);
    leanh::lean_dec(v___y_4459_);
    return v_res_4466_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1(
    mut v_00_u03b1_4467_: *mut leanh::LeanObject,
    mut v_type_4468_: *mut leanh::LeanObject,
    mut v_k_4469_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4470_: u8,
    mut v___y_4471_: *mut leanh::LeanObject,
    mut v___y_4472_: *mut leanh::LeanObject,
    mut v___y_4473_: *mut leanh::LeanObject,
    mut v___y_4474_: *mut leanh::LeanObject,
    mut v___y_4475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4477_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1___redArg(v_type_4468_, v_k_4469_, v_cleanupAnnotations_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
    return v___x_4477_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1___boxed(
    mut v_00_u03b1_4478_: *mut leanh::LeanObject,
    mut v_type_4479_: *mut leanh::LeanObject,
    mut v_k_4480_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4481_: *mut leanh::LeanObject,
    mut v___y_4482_: *mut leanh::LeanObject,
    mut v___y_4483_: *mut leanh::LeanObject,
    mut v___y_4484_: *mut leanh::LeanObject,
    mut v___y_4485_: *mut leanh::LeanObject,
    mut v___y_4486_: *mut leanh::LeanObject,
    mut v___y_4487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4488_: u8 = 0;
    let mut v_res_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4488_ = (leanh::lean_unbox(v_cleanupAnnotations_4481_) as u8);
    v_res_4489_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1(v_00_u03b1_4478_, v_type_4479_, v_k_4480_, v_cleanupAnnotations_boxed_4488_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
    leanh::lean_dec(v___y_4486_);
    leanh::lean_dec_ref(v___y_4485_);
    leanh::lean_dec(v___y_4484_);
    leanh::lean_dec_ref(v___y_4483_);
    leanh::lean_dec(v___y_4482_);
    return v_res_4489_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit___lam__0___boxed(
    mut v_x_4490_: *mut leanh::LeanObject,
    mut v_type_4491_: *mut leanh::LeanObject,
    mut v___y_4492_: *mut leanh::LeanObject,
    mut v___y_4493_: *mut leanh::LeanObject,
    mut v___y_4494_: *mut leanh::LeanObject,
    mut v___y_4495_: *mut leanh::LeanObject,
    mut v___y_4496_: *mut leanh::LeanObject,
    mut v___y_4497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4498_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit___lam__0(v_x_4490_, v_type_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
    leanh::lean_dec(v___y_4496_);
    leanh::lean_dec_ref(v___y_4495_);
    leanh::lean_dec(v___y_4494_);
    leanh::lean_dec_ref(v___y_4493_);
    leanh::lean_dec(v___y_4492_);
    leanh::lean_dec_ref(v_x_4490_);
    return v_res_4498_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit(
    mut v_type_4499_: *mut leanh::LeanObject,
    mut v_a_4500_: *mut leanh::LeanObject,
    mut v_a_4501_: *mut leanh::LeanObject,
    mut v_a_4502_: *mut leanh::LeanObject,
    mut v_a_4503_: *mut leanh::LeanObject,
    mut v_a_4504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4508_: u8 = 0;
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: u8 = 0;
    let mut v___x_4515_: u8 = 0;
    let mut v___f_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: u8 = 0;
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v_val_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4542_: u8 = 0;
    let mut v_a_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4548_: u8 = 0;
    let mut v_a_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: u8 = 0;
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4560_: u8 = 0;
    let mut v___x_4561_: u8 = 0;
    let mut v___x_4562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4516_ = leanh::lean_alloc_closure(l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit___lam__0___boxed as *mut core::ffi::c_void, 8, 0);
                leanh::lean_inc_ref(v_type_4499_);
                v___x_4557_ = l_Lean_Meta_whnfCoreUnfoldingAnnotations(
                    v_type_4499_,
                    v_a_4501_,
                    v_a_4502_,
                    v_a_4503_,
                    v_a_4504_,
                );
                if leanh::lean_obj_tag(v___x_4557_) == 0 {
                    leanh::lean_dec_ref(v_type_4499_);
                    v___y_4554_ = v___x_4557_;
                    state = 8;
                    continue;
                } else {
                    v_a_4558_ = leanh::lean_ctor_get(v___x_4557_, 0);
                    leanh::lean_inc(v_a_4558_);
                    v___x_4561_ = l_Lean_Exception_isInterrupt(v_a_4558_);
                    if v___x_4561_ == 0 {
                        v___x_4562_ = l_Lean_Exception_isRuntime(v_a_4558_);
                        v___y_4560_ = v___x_4562_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_4558_);
                        v___y_4560_ = v___x_4561_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_4508_ == 0 {
                    leanh::lean_dec_ref(v___y_4507_);
                    v___x_4509_ = leanh::lean_box(0);
                    v___x_4510_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4510_, 0, v___x_4509_);
                    return v___x_4510_;
                } else {
                    v___x_4511_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4511_, 0, v___y_4507_);
                    return v___x_4511_;
                }
            }
            2 => {
                v___x_4514_ = l_Lean_Exception_isInterrupt(v_a_4513_);
                if v___x_4514_ == 0 {
                    leanh::lean_inc_ref(v_a_4513_);
                    v___x_4515_ = l_Lean_Exception_isRuntime(v_a_4513_);
                    v___y_4507_ = v_a_4513_;
                    v___y_4508_ = v___x_4515_;
                    state = 1;
                    continue;
                } else {
                    v___y_4507_ = v_a_4513_;
                    v___y_4508_ = v___x_4514_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4519_ = l_Lean_Expr_isForall(v_a_4518_);
                if v___x_4519_ == 0 {
                    leanh::lean_dec_ref(v___f_4516_);
                    v___x_4520_ = l_Lean_instantiateMVars___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__0___redArg(v_a_4518_, v_a_4502_);
                    if leanh::lean_obj_tag(v___x_4520_) == 0 {
                        v_a_4521_ = leanh::lean_ctor_get(v___x_4520_, 0);
                        v_isSharedCheck_4548_ =
                            (!leanh::lean_is_exclusive(v___x_4520_)) as u8;
                        if v_isSharedCheck_4548_ == 0 {
                            v___x_4523_ = v___x_4520_;
                            v_isShared_4524_ = v_isSharedCheck_4548_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4521_);
                            leanh::lean_dec(v___x_4520_);
                            v___x_4523_ = leanh::lean_box(0);
                            v_isShared_4524_ = v_isSharedCheck_4548_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_4549_ = leanh::lean_ctor_get(v___x_4520_, 0);
                        leanh::lean_inc(v_a_4549_);
                        leanh::lean_dec_ref_known(v___x_4520_, 1);
                        v_a_4513_ = v_a_4549_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4550_ = 0;
                    v___x_4551_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit_spec__1___redArg(v_a_4518_, v___f_4516_, v___x_4550_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
                    if leanh::lean_obj_tag(v___x_4551_) == 0 {
                        return v___x_4551_;
                    } else {
                        v_a_4552_ = leanh::lean_ctor_get(v___x_4551_, 0);
                        leanh::lean_inc(v_a_4552_);
                        leanh::lean_dec_ref_known(v___x_4551_, 1);
                        v_a_4513_ = v_a_4552_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4525_ = l_Lean_Expr_getAppFn(v_a_4521_);
                if leanh::lean_obj_tag(v___x_4525_) == 4 {
                    leanh::lean_del_object(v___x_4523_);
                    v_declName_4526_ = leanh::lean_ctor_get(v___x_4525_, 0);
                    leanh::lean_inc(v_declName_4526_);
                    leanh::lean_dec_ref_known(v___x_4525_, 2);
                    v___x_4527_ = lean_st_ref_take(v_a_4500_);
                    v___x_4528_ = lean_array_push(v___x_4527_, v_declName_4526_);
                    v___x_4529_ = lean_st_ref_set(v_a_4500_, v___x_4528_);
                    v___x_4530_ = l_Lean_Server_Completion_unfoldDefinitionGuarded_x3f(
                        v_a_4521_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_,
                    );
                    if leanh::lean_obj_tag(v___x_4530_) == 0 {
                        v_a_4531_ = leanh::lean_ctor_get(v___x_4530_, 0);
                        v_isSharedCheck_4542_ =
                            (!leanh::lean_is_exclusive(v___x_4530_)) as u8;
                        if v_isSharedCheck_4542_ == 0 {
                            v___x_4533_ = v___x_4530_;
                            v_isShared_4534_ = v_isSharedCheck_4542_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4531_);
                            leanh::lean_dec(v___x_4530_);
                            v___x_4533_ = leanh::lean_box(0);
                            v_isShared_4534_ = v_isSharedCheck_4542_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_4543_ = leanh::lean_ctor_get(v___x_4530_, 0);
                        leanh::lean_inc(v_a_4543_);
                        leanh::lean_dec_ref_known(v___x_4530_, 1);
                        v_a_4513_ = v_a_4543_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4525_);
                    leanh::lean_dec(v_a_4521_);
                    v___x_4544_ = leanh::lean_box(0);
                    if v_isShared_4524_ == 0 {
                        leanh::lean_ctor_set(v___x_4523_, 0, v___x_4544_);
                        v___x_4546_ = v___x_4523_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4547_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4547_, 0, v___x_4544_);
                        v___x_4546_ = v_reuseFailAlloc_4547_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_4531_) == 1 {
                    leanh::lean_del_object(v___x_4533_);
                    v_val_4535_ = leanh::lean_ctor_get(v_a_4531_, 0);
                    leanh::lean_inc(v_val_4535_);
                    leanh::lean_dec_ref_known(v_a_4531_, 1);
                    v___x_4536_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit(v_val_4535_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
                    if leanh::lean_obj_tag(v___x_4536_) == 0 {
                        return v___x_4536_;
                    } else {
                        v_a_4537_ = leanh::lean_ctor_get(v___x_4536_, 0);
                        leanh::lean_inc(v_a_4537_);
                        leanh::lean_dec_ref_known(v___x_4536_, 1);
                        v_a_4513_ = v_a_4537_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4531_);
                    v___x_4538_ = leanh::lean_box(0);
                    if v_isShared_4534_ == 0 {
                        leanh::lean_ctor_set(v___x_4533_, 0, v___x_4538_);
                        v___x_4540_ = v___x_4533_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4541_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 0, v___x_4538_);
                        v___x_4540_ = v_reuseFailAlloc_4541_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4540_;
            }
            7 => {
                return v___x_4546_;
            }
            8 => {
                if leanh::lean_obj_tag(v___y_4554_) == 0 {
                    v_a_4555_ = leanh::lean_ctor_get(v___y_4554_, 0);
                    leanh::lean_inc(v_a_4555_);
                    leanh::lean_dec_ref_known(v___y_4554_, 1);
                    v_a_4518_ = v_a_4555_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___f_4516_);
                    v_a_4556_ = leanh::lean_ctor_get(v___y_4554_, 0);
                    leanh::lean_inc(v_a_4556_);
                    leanh::lean_dec_ref_known(v___y_4554_, 1);
                    v_a_4513_ = v_a_4556_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                if v___y_4560_ == 0 {
                    leanh::lean_dec_ref_known(v___x_4557_, 1);
                    v_a_4518_ = v_type_4499_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_type_4499_);
                    v___y_4554_ = v___x_4557_;
                    state = 8;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit___lam__0(
    mut v_x_4563_: *mut leanh::LeanObject,
    mut v_type_4564_: *mut leanh::LeanObject,
    mut v___y_4565_: *mut leanh::LeanObject,
    mut v___y_4566_: *mut leanh::LeanObject,
    mut v___y_4567_: *mut leanh::LeanObject,
    mut v___y_4568_: *mut leanh::LeanObject,
    mut v___y_4569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4571_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit(v_type_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
    return v___x_4571_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit___boxed(
    mut v_type_4572_: *mut leanh::LeanObject,
    mut v_a_4573_: *mut leanh::LeanObject,
    mut v_a_4574_: *mut leanh::LeanObject,
    mut v_a_4575_: *mut leanh::LeanObject,
    mut v_a_4576_: *mut leanh::LeanObject,
    mut v_a_4577_: *mut leanh::LeanObject,
    mut v_a_4578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4579_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit(v_type_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_);
    leanh::lean_dec(v_a_4577_);
    leanh::lean_dec_ref(v_a_4576_);
    leanh::lean_dec(v_a_4575_);
    leanh::lean_dec_ref(v_a_4574_);
    leanh::lean_dec(v_a_4573_);
    return v_res_4579_;
}
pub unsafe fn l_Lean_Server_Completion_getDotIdCompletionTypeNames(
    mut v_type_4580_: *mut leanh::LeanObject,
    mut v_a_4581_: *mut leanh::LeanObject,
    mut v_a_4582_: *mut leanh::LeanObject,
    mut v_a_4583_: *mut leanh::LeanObject,
    mut v_a_4584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4591_: u8 = 0;
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4596_: u8 = 0;
    let mut v_unused_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4601_: u8 = 0;
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mergeStructureResolutionOrders___at___00Lean_computeStructureResolutionOrder___at___00Lean_getStructureResolutionOrder___at___00Lean_getAllParentStructures___at___00__private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotCompletionTypeNames_visit_spec__0_spec__0_spec__1_spec__4_spec__10___closed__0;
                v___x_4587_ = lean_st_mk_ref(v___x_4586_);
                v___x_4588_ = l___private_Lean_Server_Completion_CompletionUtils_0__Lean_Server_Completion_getDotIdCompletionTypeNames_visit(v_type_4580_, v___x_4587_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_);
                if leanh::lean_obj_tag(v___x_4588_) == 0 {
                    v_isSharedCheck_4596_ = (!leanh::lean_is_exclusive(v___x_4588_)) as u8;
                    if v_isSharedCheck_4596_ == 0 {
                        v_unused_4597_ = leanh::lean_ctor_get(v___x_4588_, 0);
                        leanh::lean_dec(v_unused_4597_);
                        v___x_4590_ = v___x_4588_;
                        v_isShared_4591_ = v_isSharedCheck_4596_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4588_);
                        v___x_4590_ = leanh::lean_box(0);
                        v_isShared_4591_ = v_isSharedCheck_4596_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4587_);
                    v_a_4598_ = leanh::lean_ctor_get(v___x_4588_, 0);
                    v_isSharedCheck_4605_ = (!leanh::lean_is_exclusive(v___x_4588_)) as u8;
                    if v_isSharedCheck_4605_ == 0 {
                        v___x_4600_ = v___x_4588_;
                        v_isShared_4601_ = v_isSharedCheck_4605_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4598_);
                        leanh::lean_dec(v___x_4588_);
                        v___x_4600_ = leanh::lean_box(0);
                        v_isShared_4601_ = v_isSharedCheck_4605_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4592_ = lean_st_ref_get(v___x_4587_);
                leanh::lean_dec(v___x_4587_);
                if v_isShared_4591_ == 0 {
                    leanh::lean_ctor_set(v___x_4590_, 0, v___x_4592_);
                    v___x_4594_ = v___x_4590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4595_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4592_);
                    v___x_4594_ = v_reuseFailAlloc_4595_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4594_;
            }
            3 => {
                if v_isShared_4601_ == 0 {
                    v___x_4603_ = v___x_4600_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4604_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4604_, 0, v_a_4598_);
                    v___x_4603_ = v_reuseFailAlloc_4604_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Server_Completion_getDotIdCompletionTypeNames___boxed(
    mut v_type_4606_: *mut leanh::LeanObject,
    mut v_a_4607_: *mut leanh::LeanObject,
    mut v_a_4608_: *mut leanh::LeanObject,
    mut v_a_4609_: *mut leanh::LeanObject,
    mut v_a_4610_: *mut leanh::LeanObject,
    mut v_a_4611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4612_ = l_Lean_Server_Completion_getDotIdCompletionTypeNames(
        v_type_4606_,
        v_a_4607_,
        v_a_4608_,
        v_a_4609_,
        v_a_4610_,
    );
    leanh::lean_dec(v_a_4610_);
    leanh::lean_dec_ref(v_a_4609_);
    leanh::lean_dec(v_a_4608_);
    leanh::lean_dec_ref(v_a_4607_);
    return v_res_4612_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Completion_CompletionUtils(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Completion_CompletionUtils(
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
pub unsafe fn initialize_Lean_Server_Completion_CompletionUtils(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_CompletionUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Completion_CompletionUtils(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Completion_CompletionUtils(builtin);
}