// Lean compiler output
// Module: Lean.Compiler.LCNF.ToImpureType
// Imports: Lean.Compiler.LCNF.Irrelevant Lean.Compiler.LCNF.MonoTypes Init.Data.Format.Macro
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uset, lean_expr_dbg_to_string, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_dec_eq, lean_uint64_of_nat,
    lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_Name_str___override,
    l_List_lengthTR___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::BaseTypes::l_Lean_Compiler_LCNF_getOtherDeclBaseType;
use crate::r#gen::Lean::Compiler::LCNF::Basic::l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
use crate::r#gen::Lean::Compiler::LCNF::Irrelevant::{
    initialize_Lean_Compiler_LCNF_Irrelevant,
    l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f,
    runtime_initialize_Lean_Compiler_LCNF_Irrelevant,
};
use crate::r#gen::Lean::Compiler::LCNF::MonoTypes::{
    initialize_Lean_Compiler_LCNF_MonoTypes, l_Lean_Compiler_LCNF_getParamTypes,
    l_Lean_Compiler_LCNF_toMonoType, runtime_initialize_Lean_Compiler_LCNF_MonoTypes,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_instantiateForall, l_Lean_Compiler_LCNF_toLCNFType, l_Lean_Expr_isErased,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_instInhabitedCoreM___lam__0___boxed;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg, l_Lean_PersistentHashMap_instInhabited,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_Environment_find_x3f,
    l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_const___override,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_FVarId_getType___redArg, l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProp, l_Lean_Meta_isTypeFormerType};
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 103, 103, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0_value) as *mut leanh::LeanObject,13921617720798624167 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 51, 50, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3_value) as *mut leanh::LeanObject,13474504806189678690 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 49, 54, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6_value) as *mut leanh::LeanObject,9755723410228041222 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 73, 110, 116, 56, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9_value) as *mut leanh::LeanObject,15764114953608429200 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__0_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__1_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [76, 101, 97, 110, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 46, 102, 105, 110, 100, 33, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__2_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 97, 112, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [83, 117, 98, 116, 121, 112, 101, 0],
};
static mut l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__1_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [86, 111, 105, 100, 0],
};
static mut l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__2_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [110, 111, 110, 101, 109, 112, 116, 121, 84, 121, 112, 101, 0],
};
static mut l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__0_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 84, 111, 73, 109, 112, 117, 114, 101, 84, 121, 112, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__1_value: leanh::LeanStringObject<89> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 84, 111, 73, 109, 112, 117, 114, 101, 84, 121, 112, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 110, 97, 109, 101, 84, 111, 73, 109, 112, 117, 114, 101, 84, 121, 112, 101, 46, 102, 105, 108, 108, 67, 97, 99, 104, 101, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut leanh::LeanObject,72621647814721793 as *mut leanh::LeanObject,65793 as *mut leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__5: u64 = 0;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__12_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 111, 98, 106, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__0_value) as *mut leanh::LeanObject,930430701391226905 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [111, 98, 106, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__3_value) as *mut leanh::LeanObject,6552590064380865520 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__6_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [85, 73, 110, 116, 54, 52, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [85, 83, 105, 122, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__8_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 108, 111, 97, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__9_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [70, 108, 111, 97, 116, 51, 50, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__10_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [108, 99, 69, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__11_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__12_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 99, 86, 111, 105, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__12_value) as *mut leanh::LeanObject,12548675615898448964 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__10_value) as *mut leanh::LeanObject,381462102099548843 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__15_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__17_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__9_value) as *mut leanh::LeanObject,16690552700474419446 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__17_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__8_value) as *mut leanh::LeanObject,4889978610488853816 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__19_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__20_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__21_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__7_value) as *mut leanh::LeanObject,17712594561405737325 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__21_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__22_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__22: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__6_value) as *mut leanh::LeanObject,2954612489107370298 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__23_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 99, 65, 110, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_toImpureType___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Compiler_LCNF_toImpureType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpureType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toImpureType___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toImpureType___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_toImpureType___closed__2_value: leanh::LeanStringObject<32> =
    leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            116, 111, 73, 109, 112, 117, 114, 101, 84, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_toImpureType___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_toImpureType___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_toImpureType___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toImpureType___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_toImpureType___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_toImpureType___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 151, 190, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 98, 106, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__4_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__6_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 115, 105, 122, 101, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__6_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__8_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [115, 99, 97, 108, 97, 114, 35, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__8_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__10_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__10_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [118, 111, 105, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__12_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_instToFormat___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0_value:
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
static mut l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_instInhabitedCtorLayout: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__2___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0_value: leanh::LeanStringObject<86> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 86, m_capacity: 86, m_length: 85, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 84, 111, 73, 109, 112, 117, 114, 101, 84, 121, 112, 101, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 103, 101, 116, 67, 116, 111, 114, 76, 97, 121, 111, 117, 116, 46, 102, 105, 108, 108, 67, 97, 99, 104, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2549_ = leanh::lean_box(0);
    v___x_2550_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__1;
    v___x_2551_ = l_Lean_Expr_const___override(v___x_2550_, v___x_2549_);
    return v___x_2551_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2555_ = leanh::lean_box(0);
    v___x_2556_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4;
    v___x_2557_ = l_Lean_Expr_const___override(v___x_2556_, v___x_2555_);
    return v___x_2557_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2561_ = leanh::lean_box(0);
    v___x_2562_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7;
    v___x_2563_ = l_Lean_Expr_const___override(v___x_2562_, v___x_2561_);
    return v___x_2563_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2567_ = leanh::lean_box(0);
    v___x_2568_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10;
    v___x_2569_ = l_Lean_Expr_const___override(v___x_2568_, v___x_2567_);
    return v___x_2569_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum(
    mut v_numCtors_2570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: u8 = 0;
    v___x_2571_ = leanh::lean_unsigned_to_nat(1);
    v___x_2572_ = lean_nat_dec_eq(v_numCtors_2570_, v___x_2571_);
    if v___x_2572_ == 0 {
        let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: u8 = 0;
        v___x_2573_ = leanh::lean_unsigned_to_nat(256);
        v___x_2574_ = lean_nat_dec_lt(v_numCtors_2570_, v___x_2573_);
        if v___x_2574_ == 0 {
            let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2576_: u8 = 0;
            v___x_2575_ = leanh::lean_unsigned_to_nat(65536);
            v___x_2576_ = lean_nat_dec_lt(v_numCtors_2570_, v___x_2575_);
            if v___x_2576_ == 0 {
                let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2578_: u8 = 0;
                v___x_2577_ = leanh::lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
                v___x_2578_ = lean_nat_dec_lt(v_numCtors_2570_, v___x_2577_);
                if v___x_2578_ == 0 {
                    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2579_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2);
                    return v___x_2579_;
                } else {
                    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_2580_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5);
                    return v___x_2580_;
                }
            } else {
                let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_2581_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8);
                return v___x_2581_;
            }
        } else {
            let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2582_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11);
            return v___x_2582_;
        }
    } else {
        let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2583_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__2);
        return v___x_2583_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___boxed(
    mut v_numCtors_2584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2585_ =
        l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum(
            v_numCtors_2584_,
        );
    leanh::lean_dec(v_numCtors_2584_);
    return v_res_2585_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__2(
    mut v_msg_2586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2587_ = l_Lean_instInhabitedExpr;
    v___x_2588_ = lean_panic_fn_borrowed(v___x_2587_, v_msg_2586_);
    return v___x_2588_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_x_2589_: *mut leanh::LeanObject,
    mut v_x_2590_: *mut leanh::LeanObject,
    mut v_x_2591_: *mut leanh::LeanObject,
    mut v_x_2592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2597_: u8 = 0;
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: u8 = 0;
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: u8 = 0;
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2593_ = leanh::lean_ctor_get(v_x_2589_, 0);
                v_vs_2594_ = leanh::lean_ctor_get(v_x_2589_, 1);
                v_isSharedCheck_2618_ = (!leanh::lean_is_exclusive(v_x_2589_)) as u8;
                if v_isSharedCheck_2618_ == 0 {
                    v___x_2596_ = v_x_2589_;
                    v_isShared_2597_ = v_isSharedCheck_2618_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2594_);
                    leanh::lean_inc(v_ks_2593_);
                    leanh::lean_dec(v_x_2589_);
                    v___x_2596_ = leanh::lean_box(0);
                    v_isShared_2597_ = v_isSharedCheck_2618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2598_ = lean_array_get_size(v_ks_2593_);
                v___x_2599_ = lean_nat_dec_lt(v_x_2590_, v___x_2598_);
                if v___x_2599_ == 0 {
                    leanh::lean_dec(v_x_2590_);
                    v___x_2600_ = lean_array_push(v_ks_2593_, v_x_2591_);
                    v___x_2601_ = lean_array_push(v_vs_2594_, v_x_2592_);
                    if v_isShared_2597_ == 0 {
                        leanh::lean_ctor_set(v___x_2596_, 1, v___x_2601_);
                        leanh::lean_ctor_set(v___x_2596_, 0, v___x_2600_);
                        v___x_2603_ = v___x_2596_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2604_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2600_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2601_);
                        v___x_2603_ = v_reuseFailAlloc_2604_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2605_ = lean_array_fget_borrowed(v_ks_2593_, v_x_2590_);
                    v___x_2606_ = lean_name_eq(v_x_2591_, v_k_x27_2605_);
                    if v___x_2606_ == 0 {
                        if v_isShared_2597_ == 0 {
                            v___x_2608_ = v___x_2596_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2612_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_ks_2593_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_vs_2594_);
                            v___x_2608_ = v_reuseFailAlloc_2612_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2613_ = lean_array_fset(v_ks_2593_, v_x_2590_, v_x_2591_);
                        v___x_2614_ = lean_array_fset(v_vs_2594_, v_x_2590_, v_x_2592_);
                        leanh::lean_dec(v_x_2590_);
                        if v_isShared_2597_ == 0 {
                            leanh::lean_ctor_set(v___x_2596_, 1, v___x_2614_);
                            leanh::lean_ctor_set(v___x_2596_, 0, v___x_2613_);
                            v___x_2616_ = v___x_2596_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2617_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2613_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2614_);
                            v___x_2616_ = v_reuseFailAlloc_2617_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2603_;
            }
            3 => {
                v___x_2609_ = leanh::lean_unsigned_to_nat(1);
                v___x_2610_ = lean_nat_add(v_x_2590_, v___x_2609_);
                leanh::lean_dec(v_x_2590_);
                v_x_2589_ = v___x_2608_;
                v_x_2590_ = v___x_2610_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_n_2619_: *mut leanh::LeanObject,
    mut v_k_2620_: *mut leanh::LeanObject,
    mut v_v_2621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2622_ = leanh::lean_unsigned_to_nat(0);
    v___x_2623_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_n_2619_, v___x_2622_, v_k_2620_, v_v_2621_);
    return v___x_2623_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0()
-> u64 {
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: u64 = 0;
    v___x_2624_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2625_ = lean_uint64_of_nat(v___x_2624_);
    return v___x_2625_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_2626_: usize = 0;
    let mut v___x_2627_: usize = 0;
    let mut v___x_2628_: usize = 0;
    v___x_2626_ = 5usize;
    v___x_2627_ = 1usize;
    v___x_2628_ = lean_usize_shift_left(v___x_2627_, v___x_2626_);
    return v___x_2628_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_2629_: usize = 0;
    let mut v___x_2630_: usize = 0;
    let mut v___x_2631_: usize = 0;
    v___x_2629_ = 1usize;
    v___x_2630_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_2631_ = lean_usize_sub(v___x_2630_, v___x_2629_);
    return v___x_2631_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2632_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2632_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_x_2633_: *mut leanh::LeanObject,
    mut v_x_2634_: usize,
    mut v_x_2635_: usize,
    mut v_x_2636_: *mut leanh::LeanObject,
    mut v_x_2637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: usize = 0;
    let mut v___x_2640_: usize = 0;
    let mut v___x_2641_: usize = 0;
    let mut v___x_2642_: usize = 0;
    let mut v_j_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: u8 = 0;
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2648_: u8 = 0;
    let mut v_v_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2662_: u8 = 0;
    let mut v___x_2663_: u8 = 0;
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2669_: u8 = 0;
    let mut v_node_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2673_: u8 = 0;
    let mut v___x_2674_: usize = 0;
    let mut v___x_2675_: usize = 0;
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2680_: u8 = 0;
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2682_: u8 = 0;
    let mut v_unused_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2693_: u8 = 0;
    let mut v_ks_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: usize = 0;
    let mut v___x_2700_: u8 = 0;
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: u8 = 0;
    let mut v_reuseFailAlloc_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2633_) == 0 {
                    v_es_2638_ = leanh::lean_ctor_get(v_x_2633_, 0);
                    v___x_2639_ = 5usize;
                    v___x_2640_ = 1usize;
                    v___x_2641_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_2642_ = lean_usize_land(v_x_2634_, v___x_2641_);
                    v_j_2643_ = lean_usize_to_nat(v___x_2642_);
                    v___x_2644_ = lean_array_get_size(v_es_2638_);
                    v___x_2645_ = lean_nat_dec_lt(v_j_2643_, v___x_2644_);
                    if v___x_2645_ == 0 {
                        leanh::lean_dec(v_j_2643_);
                        leanh::lean_dec(v_x_2637_);
                        leanh::lean_dec(v_x_2636_);
                        return v_x_2633_;
                    } else {
                        leanh::lean_inc_ref(v_es_2638_);
                        v_isSharedCheck_2682_ = (!leanh::lean_is_exclusive(v_x_2633_)) as u8;
                        if v_isSharedCheck_2682_ == 0 {
                            v_unused_2683_ = leanh::lean_ctor_get(v_x_2633_, 0);
                            leanh::lean_dec(v_unused_2683_);
                            v___x_2647_ = v_x_2633_;
                            v_isShared_2648_ = v_isSharedCheck_2682_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2633_);
                            v___x_2647_ = leanh::lean_box(0);
                            v_isShared_2648_ = v_isSharedCheck_2682_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2684_ = leanh::lean_ctor_get(v_x_2633_, 0);
                    v_vs_2685_ = leanh::lean_ctor_get(v_x_2633_, 1);
                    v_isSharedCheck_2705_ = (!leanh::lean_is_exclusive(v_x_2633_)) as u8;
                    if v_isSharedCheck_2705_ == 0 {
                        v___x_2687_ = v_x_2633_;
                        v_isShared_2688_ = v_isSharedCheck_2705_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2685_);
                        leanh::lean_inc(v_ks_2684_);
                        leanh::lean_dec(v_x_2633_);
                        v___x_2687_ = leanh::lean_box(0);
                        v_isShared_2688_ = v_isSharedCheck_2705_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2649_ = lean_array_fget(v_es_2638_, v_j_2643_);
                v___x_2650_ = leanh::lean_box(0);
                v_xs_x27_2651_ = lean_array_fset(v_es_2638_, v_j_2643_, v___x_2650_);
                match leanh::lean_obj_tag(v_v_2649_) {
                    0 => {
                        v_key_2658_ = leanh::lean_ctor_get(v_v_2649_, 0);
                        v_val_2659_ = leanh::lean_ctor_get(v_v_2649_, 1);
                        v_isSharedCheck_2669_ = (!leanh::lean_is_exclusive(v_v_2649_)) as u8;
                        if v_isSharedCheck_2669_ == 0 {
                            v___x_2661_ = v_v_2649_;
                            v_isShared_2662_ = v_isSharedCheck_2669_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2659_);
                            leanh::lean_inc(v_key_2658_);
                            leanh::lean_dec(v_v_2649_);
                            v___x_2661_ = leanh::lean_box(0);
                            v_isShared_2662_ = v_isSharedCheck_2669_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2670_ = leanh::lean_ctor_get(v_v_2649_, 0);
                        v_isSharedCheck_2680_ = (!leanh::lean_is_exclusive(v_v_2649_)) as u8;
                        if v_isSharedCheck_2680_ == 0 {
                            v___x_2672_ = v_v_2649_;
                            v_isShared_2673_ = v_isSharedCheck_2680_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2670_);
                            leanh::lean_dec(v_v_2649_);
                            v___x_2672_ = leanh::lean_box(0);
                            v_isShared_2673_ = v_isSharedCheck_2680_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2681_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2681_, 0, v_x_2636_);
                        leanh::lean_ctor_set(v___x_2681_, 1, v_x_2637_);
                        v___y_2653_ = v___x_2681_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2654_ = lean_array_fset(v_xs_x27_2651_, v_j_2643_, v___y_2653_);
                leanh::lean_dec(v_j_2643_);
                if v_isShared_2648_ == 0 {
                    leanh::lean_ctor_set(v___x_2647_, 0, v___x_2654_);
                    v___x_2656_ = v___x_2647_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2654_);
                    v___x_2656_ = v_reuseFailAlloc_2657_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2656_;
            }
            4 => {
                v___x_2663_ = lean_name_eq(v_x_2636_, v_key_2658_);
                if v___x_2663_ == 0 {
                    leanh::lean_del_object(v___x_2661_);
                    v___x_2664_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2658_,
                        v_val_2659_,
                        v_x_2636_,
                        v_x_2637_,
                    );
                    v___x_2665_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2665_, 0, v___x_2664_);
                    v___y_2653_ = v___x_2665_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2659_);
                    leanh::lean_dec(v_key_2658_);
                    if v_isShared_2662_ == 0 {
                        leanh::lean_ctor_set(v___x_2661_, 1, v_x_2637_);
                        leanh::lean_ctor_set(v___x_2661_, 0, v_x_2636_);
                        v___x_2667_ = v___x_2661_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2668_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_x_2636_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_x_2637_);
                        v___x_2667_ = v_reuseFailAlloc_2668_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2653_ = v___x_2667_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2674_ = lean_usize_shift_right(v_x_2634_, v___x_2639_);
                v___x_2675_ = lean_usize_add(v_x_2635_, v___x_2640_);
                v___x_2676_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_node_2670_, v___x_2674_, v___x_2675_, v_x_2636_, v_x_2637_);
                if v_isShared_2673_ == 0 {
                    leanh::lean_ctor_set(v___x_2672_, 0, v___x_2676_);
                    v___x_2678_ = v___x_2672_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2679_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2676_);
                    v___x_2678_ = v_reuseFailAlloc_2679_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2653_ = v___x_2678_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2688_ == 0 {
                    v___x_2690_ = v___x_2687_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2704_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_ks_2684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_vs_2685_);
                    v___x_2690_ = v_reuseFailAlloc_2704_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2691_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v___x_2690_, v_x_2636_, v_x_2637_);
                v___x_2699_ = 7usize;
                v___x_2700_ = lean_usize_dec_le(v___x_2699_, v_x_2635_);
                if v___x_2700_ == 0 {
                    v___x_2701_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2691_);
                    v___x_2702_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2703_ = lean_nat_dec_lt(v___x_2701_, v___x_2702_);
                    leanh::lean_dec(v___x_2701_);
                    v___y_2693_ = v___x_2703_;
                    state = 10;
                    continue;
                } else {
                    v___y_2693_ = v___x_2700_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2693_ == 0 {
                    v_ks_2694_ = leanh::lean_ctor_get(v_newNode_2691_, 0);
                    leanh::lean_inc_ref(v_ks_2694_);
                    v_vs_2695_ = leanh::lean_ctor_get(v_newNode_2691_, 1);
                    leanh::lean_inc_ref(v_vs_2695_);
                    leanh::lean_dec_ref(v_newNode_2691_);
                    v___x_2696_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2697_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_2698_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_x_2635_, v_ks_2694_, v_vs_2695_, v___x_2696_, v___x_2697_);
                    leanh::lean_dec_ref(v_vs_2695_);
                    leanh::lean_dec_ref(v_ks_2694_);
                    return v___x_2698_;
                } else {
                    return v_newNode_2691_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_depth_2706_: usize,
    mut v_keys_2707_: *mut leanh::LeanObject,
    mut v_vals_2708_: *mut leanh::LeanObject,
    mut v_i_2709_: *mut leanh::LeanObject,
    mut v_entries_2710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    let mut v_k_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2716_: u64 = 0;
    let mut v_h_2717_: usize = 0;
    let mut v___x_2718_: usize = 0;
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: usize = 0;
    let mut v___x_2721_: usize = 0;
    let mut v___x_2722_: usize = 0;
    let mut v_h_2723_: usize = 0;
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: u64 = 0;
    let mut v_hash_2728_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2711_ = lean_array_get_size(v_keys_2707_);
                v___x_2712_ = lean_nat_dec_lt(v_i_2709_, v___x_2711_);
                if v___x_2712_ == 0 {
                    leanh::lean_dec(v_i_2709_);
                    return v_entries_2710_;
                } else {
                    v_k_2713_ = lean_array_fget_borrowed(v_keys_2707_, v_i_2709_);
                    v_v_2714_ = lean_array_fget_borrowed(v_vals_2708_, v_i_2709_);
                    if leanh::lean_obj_tag(v_k_2713_) == 0 {
                        v___x_2727_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
                        v___y_2716_ = v___x_2727_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_2728_ = leanh::lean_ctor_get_uint64(
                            v_k_2713_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_2716_ = v_hash_2728_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_2717_ = lean_uint64_to_usize(v___y_2716_);
                v___x_2718_ = 5usize;
                v___x_2719_ = leanh::lean_unsigned_to_nat(1);
                v___x_2720_ = 1usize;
                v___x_2721_ = lean_usize_sub(v_depth_2706_, v___x_2720_);
                v___x_2722_ = lean_usize_mul(v___x_2718_, v___x_2721_);
                v_h_2723_ = lean_usize_shift_right(v_h_2717_, v___x_2722_);
                v___x_2724_ = lean_nat_add(v_i_2709_, v___x_2719_);
                leanh::lean_dec(v_i_2709_);
                leanh::lean_inc(v_v_2714_);
                leanh::lean_inc(v_k_2713_);
                v___x_2725_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_entries_2710_, v_h_2723_, v_depth_2706_, v_k_2713_, v_v_2714_);
                v_i_2709_ = v___x_2724_;
                v_entries_2710_ = v___x_2725_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_depth_2729_: *mut leanh::LeanObject,
    mut v_keys_2730_: *mut leanh::LeanObject,
    mut v_vals_2731_: *mut leanh::LeanObject,
    mut v_i_2732_: *mut leanh::LeanObject,
    mut v_entries_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2734_: usize = 0;
    let mut v_res_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2734_ = leanh::lean_unbox_usize(v_depth_2729_);
    leanh::lean_dec(v_depth_2729_);
    v_res_2735_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_2734_, v_keys_2730_, v_vals_2731_, v_i_2732_, v_entries_2733_);
    leanh::lean_dec_ref(v_vals_2731_);
    leanh::lean_dec_ref(v_keys_2730_);
    return v_res_2735_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_2736_: *mut leanh::LeanObject,
    mut v_x_2737_: *mut leanh::LeanObject,
    mut v_x_2738_: *mut leanh::LeanObject,
    mut v_x_2739_: *mut leanh::LeanObject,
    mut v_x_2740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_656__boxed_2741_: usize = 0;
    let mut v_x_657__boxed_2742_: usize = 0;
    let mut v_res_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_656__boxed_2741_ = leanh::lean_unbox_usize(v_x_2737_);
    leanh::lean_dec(v_x_2737_);
    v_x_657__boxed_2742_ = leanh::lean_unbox_usize(v_x_2738_);
    leanh::lean_dec(v_x_2738_);
    v_res_2743_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2736_, v_x_656__boxed_2741_, v_x_657__boxed_2742_, v_x_2739_, v_x_2740_);
    return v_res_2743_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_2744_: *mut leanh::LeanObject,
    mut v_x_2745_: *mut leanh::LeanObject,
    mut v_x_2746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2748_: u64 = 0;
    let mut v___x_2749_: usize = 0;
    let mut v___x_2750_: usize = 0;
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: u64 = 0;
    let mut v_hash_2753_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2745_) == 0 {
                    v___x_2752_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
                    v___y_2748_ = v___x_2752_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2753_ = leanh::lean_ctor_get_uint64(
                        v_x_2745_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2748_ = v_hash_2753_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2749_ = lean_uint64_to_usize(v___y_2748_);
                v___x_2750_ = 1usize;
                v___x_2751_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2744_, v___x_2749_, v___x_2750_, v_x_2745_, v_x_2746_);
                return v___x_2751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_keys_2754_: *mut leanh::LeanObject,
    mut v_vals_2755_: *mut leanh::LeanObject,
    mut v_i_2756_: *mut leanh::LeanObject,
    mut v_k_2757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: u8 = 0;
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: u8 = 0;
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2758_ = lean_array_get_size(v_keys_2754_);
                v___x_2759_ = lean_nat_dec_lt(v_i_2756_, v___x_2758_);
                if v___x_2759_ == 0 {
                    leanh::lean_dec(v_i_2756_);
                    v___x_2760_ = leanh::lean_box(0);
                    return v___x_2760_;
                } else {
                    v_k_x27_2761_ = lean_array_fget_borrowed(v_keys_2754_, v_i_2756_);
                    v___x_2762_ = lean_name_eq(v_k_2757_, v_k_x27_2761_);
                    if v___x_2762_ == 0 {
                        v___x_2763_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2764_ = lean_nat_add(v_i_2756_, v___x_2763_);
                        leanh::lean_dec(v_i_2756_);
                        v_i_2756_ = v___x_2764_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2766_ = lean_array_fget_borrowed(v_vals_2755_, v_i_2756_);
                        leanh::lean_dec(v_i_2756_);
                        leanh::lean_inc(v___x_2766_);
                        v___x_2767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2767_, 0, v___x_2766_);
                        return v___x_2767_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_keys_2768_: *mut leanh::LeanObject,
    mut v_vals_2769_: *mut leanh::LeanObject,
    mut v_i_2770_: *mut leanh::LeanObject,
    mut v_k_2771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2772_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2768_, v_vals_2769_, v_i_2770_, v_k_2771_);
    leanh::lean_dec(v_k_2771_);
    leanh::lean_dec_ref(v_vals_2769_);
    leanh::lean_dec_ref(v_keys_2768_);
    return v_res_2772_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(
    mut v_x_2773_: *mut leanh::LeanObject,
    mut v_x_2774_: usize,
    mut v_x_2775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: usize = 0;
    let mut v___x_2779_: usize = 0;
    let mut v___x_2780_: usize = 0;
    let mut v_j_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: u8 = 0;
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: usize = 0;
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2773_) == 0 {
                    v_es_2776_ = leanh::lean_ctor_get(v_x_2773_, 0);
                    v___x_2777_ = leanh::lean_box(2);
                    v___x_2778_ = 5usize;
                    v___x_2779_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_2780_ = lean_usize_land(v_x_2774_, v___x_2779_);
                    v_j_2781_ = lean_usize_to_nat(v___x_2780_);
                    v___x_2782_ = lean_array_get_borrowed(v___x_2777_, v_es_2776_, v_j_2781_);
                    leanh::lean_dec(v_j_2781_);
                    match leanh::lean_obj_tag(v___x_2782_) {
                        0 => {
                            v_key_2783_ = leanh::lean_ctor_get(v___x_2782_, 0);
                            v_val_2784_ = leanh::lean_ctor_get(v___x_2782_, 1);
                            v___x_2785_ = lean_name_eq(v_x_2775_, v_key_2783_);
                            if v___x_2785_ == 0 {
                                v___x_2786_ = leanh::lean_box(0);
                                return v___x_2786_;
                            } else {
                                leanh::lean_inc(v_val_2784_);
                                v___x_2787_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2787_, 0, v_val_2784_);
                                return v___x_2787_;
                            }
                        }
                        1 => {
                            v_node_2788_ = leanh::lean_ctor_get(v___x_2782_, 0);
                            v___x_2789_ = lean_usize_shift_right(v_x_2774_, v___x_2778_);
                            v_x_2773_ = v_node_2788_;
                            v_x_2774_ = v___x_2789_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2791_ = leanh::lean_box(0);
                            return v___x_2791_;
                        }
                    }
                } else {
                    v_ks_2792_ = leanh::lean_ctor_get(v_x_2773_, 0);
                    v_vs_2793_ = leanh::lean_ctor_get(v_x_2773_, 1);
                    v___x_2794_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2795_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_ks_2792_, v_vs_2793_, v___x_2794_, v_x_2775_);
                    return v___x_2795_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_2796_: *mut leanh::LeanObject,
    mut v_x_2797_: *mut leanh::LeanObject,
    mut v_x_2798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_867__boxed_2799_: usize = 0;
    let mut v_res_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_867__boxed_2799_ = leanh::lean_unbox_usize(v_x_2797_);
    leanh::lean_dec(v_x_2797_);
    v_res_2800_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2796_, v_x_867__boxed_2799_, v_x_2798_);
    leanh::lean_dec(v_x_2798_);
    leanh::lean_dec_ref(v_x_2796_);
    return v_res_2800_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_x_2801_: *mut leanh::LeanObject,
    mut v_x_2802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2804_: u64 = 0;
    let mut v___x_2805_: usize = 0;
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: u64 = 0;
    let mut v_hash_2808_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2802_) == 0 {
                    v___x_2807_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
                    v___y_2804_ = v___x_2807_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2808_ = leanh::lean_ctor_get_uint64(
                        v_x_2802_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2804_ = v_hash_2808_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2805_ = lean_uint64_to_usize(v___y_2804_);
                v___x_2806_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2801_, v___x_2805_, v_x_2802_);
                return v___x_2806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(
    mut v_x_2809_: *mut leanh::LeanObject,
    mut v_x_2810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2811_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_2809_, v_x_2810_);
    leanh::lean_dec(v_x_2810_);
    leanh::lean_dec_ref(v_x_2809_);
    return v_res_2811_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2815_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__2;
    v___x_2816_ = leanh::lean_unsigned_to_nat(14);
    v___x_2817_ = leanh::lean_unsigned_to_nat(177);
    v___x_2818_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__1;
    v___x_2819_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__0;
    v___x_2820_ = l_mkPanicMessageWithDecl(
        v___x_2819_,
        v___x_2818_,
        v___x_2817_,
        v___x_2816_,
        v___x_2815_,
    );
    return v___x_2820_;
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3(
    mut v_newState_2821_: *mut leanh::LeanObject,
    mut v_x_2822_: *mut leanh::LeanObject,
    mut v_x_2823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2828_: u8 = 0;
    let mut v_fst_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2833_: u8 = 0;
    let mut v_snd_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2823_) == 0 {
                    return v_x_2822_;
                } else {
                    v_head_2824_ = leanh::lean_ctor_get(v_x_2823_, 0);
                    v_tail_2825_ = leanh::lean_ctor_get(v_x_2823_, 1);
                    v_isSharedCheck_2850_ = (!leanh::lean_is_exclusive(v_x_2823_)) as u8;
                    if v_isSharedCheck_2850_ == 0 {
                        v___x_2827_ = v_x_2823_;
                        v_isShared_2828_ = v_isSharedCheck_2850_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2825_);
                        leanh::lean_inc(v_head_2824_);
                        leanh::lean_dec(v_x_2823_);
                        v___x_2827_ = leanh::lean_box(0);
                        v_isShared_2828_ = v_isSharedCheck_2850_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2829_ = leanh::lean_ctor_get(v_x_2822_, 0);
                v_snd_2830_ = leanh::lean_ctor_get(v_x_2822_, 1);
                v_isSharedCheck_2849_ = (!leanh::lean_is_exclusive(v_x_2822_)) as u8;
                if v_isSharedCheck_2849_ == 0 {
                    v___x_2832_ = v_x_2822_;
                    v_isShared_2833_ = v_isSharedCheck_2849_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2830_);
                    leanh::lean_inc(v_fst_2829_);
                    leanh::lean_dec(v_x_2822_);
                    v___x_2832_ = leanh::lean_box(0);
                    v_isShared_2833_ = v_isSharedCheck_2849_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_2834_ = leanh::lean_ctor_get(v_newState_2821_, 1);
                leanh::lean_inc(v_head_2824_);
                if v_isShared_2828_ == 0 {
                    leanh::lean_ctor_set(v___x_2827_, 1, v_fst_2829_);
                    v___x_2836_ = v___x_2827_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_head_2824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_fst_2829_);
                    v___x_2836_ = v_reuseFailAlloc_2848_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2844_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_2834_, v_head_2824_);
                if leanh::lean_obj_tag(v___x_2844_) == 0 {
                    v___x_2845_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3);
                    v___x_2846_ = l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__2(v___x_2845_);
                    v___y_2838_ = v___x_2846_;
                    state = 4;
                    continue;
                } else {
                    v_val_2847_ = leanh::lean_ctor_get(v___x_2844_, 0);
                    leanh::lean_inc(v_val_2847_);
                    leanh::lean_dec_ref_known(v___x_2844_, 1);
                    v___y_2838_ = v_val_2847_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2839_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_2830_, v_head_2824_, v___y_2838_);
                if v_isShared_2833_ == 0 {
                    leanh::lean_ctor_set(v___x_2832_, 1, v___x_2839_);
                    leanh::lean_ctor_set(v___x_2832_, 0, v___x_2836_);
                    v___x_2841_ = v___x_2832_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___x_2839_);
                    v___x_2841_ = v_reuseFailAlloc_2843_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_x_2822_ = v___x_2841_;
                v_x_2823_ = v_tail_2825_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___boxed(
    mut v_newState_2851_: *mut leanh::LeanObject,
    mut v_x_2852_: *mut leanh::LeanObject,
    mut v_x_2853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2854_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3(v_newState_2851_, v_x_2852_, v_x_2853_);
    leanh::lean_dec_ref(v_newState_2851_);
    return v_res_2854_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__0(
    mut v_oldState_2857_: *mut leanh::LeanObject,
    mut v_newState_2858_: *mut leanh::LeanObject,
    mut v_x_2859_: *mut leanh::LeanObject,
    mut v_s_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2861_ = leanh::lean_ctor_get(v_newState_2858_, 0);
    v_fst_2862_ = leanh::lean_ctor_get(v_oldState_2857_, 0);
    v___x_2863_ = l_List_lengthTR___redArg(v_fst_2861_);
    v___x_2864_ = l_List_lengthTR___redArg(v_fst_2862_);
    v___x_2865_ = lean_nat_sub(v___x_2863_, v___x_2864_);
    leanh::lean_dec(v___x_2864_);
    leanh::lean_dec(v___x_2863_);
    v___x_2866_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__0___closed__0;
    leanh::lean_inc(v_fst_2861_);
    v_newEntries_2867_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        leanh::lean_box(0),
        v_fst_2861_,
        v_fst_2861_,
        v___x_2865_,
        v___x_2866_,
    );
    v___x_2868_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3(v_newState_2858_, v_s_2860_, v_newEntries_2867_);
    leanh::lean_dec_ref(v_newState_2858_);
    return v___x_2868_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__0___boxed(
    mut v_oldState_2869_: *mut leanh::LeanObject,
    mut v_newState_2870_: *mut leanh::LeanObject,
    mut v_x_2871_: *mut leanh::LeanObject,
    mut v_s_2872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2873_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__0(v_oldState_2869_, v_newState_2870_, v_x_2871_, v_s_2872_);
    leanh::lean_dec(v_x_2871_);
    leanh::lean_dec_ref(v_oldState_2869_);
    return v_res_2873_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__1(
    mut v___x_2874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2876_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2876_, 0, v___x_2874_);
    return v___x_2876_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__1___boxed(
    mut v___x_2877_: *mut leanh::LeanObject,
    mut v___y_2878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2879_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__1(v___x_2877_);
    return v_res_2879_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2881_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2881_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2882_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__1);
    v___x_2883_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2883_, 0, v___x_2882_);
    return v___x_2883_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2884_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__2);
    v___x_2885_ = leanh::lean_box(0);
    v___x_2886_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2886_, 0, v___x_2885_);
    leanh::lean_ctor_set(v___x_2886_, 1, v___x_2884_);
    return v___x_2886_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2887_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__3);
    v___f_2888_ = leanh::lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_2888_, 0, v___x_2887_);
    return v___f_2888_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0()
-> *mut leanh::LeanObject {
    let mut v___f_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2899_: u8 = 0;
    let mut v___x_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v_a_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2892_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__4_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__4);
                v___x_2893_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___closed__5;
                v___x_2894_ = leanh::lean_box(0);
                v___x_2895_ =
                    l_Lean_registerEnvExtension___redArg(v___f_2892_, v___x_2893_, v___x_2894_);
                if leanh::lean_obj_tag(v___x_2895_) == 0 {
                    v_a_2896_ = leanh::lean_ctor_get(v___x_2895_, 0);
                    v_isSharedCheck_2903_ = (!leanh::lean_is_exclusive(v___x_2895_)) as u8;
                    if v_isSharedCheck_2903_ == 0 {
                        v___x_2898_ = v___x_2895_;
                        v_isShared_2899_ = v_isSharedCheck_2903_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2896_);
                        leanh::lean_dec(v___x_2895_);
                        v___x_2898_ = leanh::lean_box(0);
                        v_isShared_2899_ = v_isSharedCheck_2903_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2904_ = leanh::lean_ctor_get(v___x_2895_, 0);
                    v_isSharedCheck_2911_ = (!leanh::lean_is_exclusive(v___x_2895_)) as u8;
                    if v_isSharedCheck_2911_ == 0 {
                        v___x_2906_ = v___x_2895_;
                        v_isShared_2907_ = v_isSharedCheck_2911_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2904_);
                        leanh::lean_dec(v___x_2895_);
                        v___x_2906_ = leanh::lean_box(0);
                        v_isShared_2907_ = v_isSharedCheck_2911_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2899_ == 0 {
                    v___x_2901_ = v___x_2898_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
                    v___x_2901_ = v_reuseFailAlloc_2902_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2901_;
            }
            3 => {
                if v_isShared_2907_ == 0 {
                    v___x_2909_ = v___x_2906_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2910_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
                    v___x_2909_ = v_reuseFailAlloc_2910_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___boxed(
    mut v_a_2912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2913_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0();
    return v_res_2913_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2915_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0();
    return v___x_2915_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2____boxed(
    mut v_a_2916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2917_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2_();
    return v_res_2917_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_2918_: *mut leanh::LeanObject,
    mut v_x_2919_: *mut leanh::LeanObject,
    mut v_x_2920_: *mut leanh::LeanObject,
    mut v_x_2921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2922_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_2919_, v_x_2920_, v_x_2921_);
    return v___x_2922_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_2923_: *mut leanh::LeanObject,
    mut v_x_2924_: *mut leanh::LeanObject,
    mut v_x_2925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2926_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_2924_, v_x_2925_);
    return v___x_2926_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_00_u03b2_2927_: *mut leanh::LeanObject,
    mut v_x_2928_: *mut leanh::LeanObject,
    mut v_x_2929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2930_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b2_2927_, v_x_2928_, v_x_2929_);
    leanh::lean_dec(v_x_2929_);
    leanh::lean_dec_ref(v_x_2928_);
    return v_res_2930_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b2_2931_: *mut leanh::LeanObject,
    mut v_x_2932_: *mut leanh::LeanObject,
    mut v_x_2933_: usize,
    mut v_x_2934_: usize,
    mut v_x_2935_: *mut leanh::LeanObject,
    mut v_x_2936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2937_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2932_, v_x_2933_, v_x_2934_, v_x_2935_, v_x_2936_);
    return v___x_2937_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2938_: *mut leanh::LeanObject,
    mut v_x_2939_: *mut leanh::LeanObject,
    mut v_x_2940_: *mut leanh::LeanObject,
    mut v_x_2941_: *mut leanh::LeanObject,
    mut v_x_2942_: *mut leanh::LeanObject,
    mut v_x_2943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1140__boxed_2944_: usize = 0;
    let mut v_x_1141__boxed_2945_: usize = 0;
    let mut v_res_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1140__boxed_2944_ = leanh::lean_unbox_usize(v_x_2940_);
    leanh::lean_dec(v_x_2940_);
    v_x_1141__boxed_2945_ = leanh::lean_unbox_usize(v_x_2941_);
    leanh::lean_dec(v_x_2941_);
    v_res_2946_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2938_, v_x_2939_, v_x_1140__boxed_2944_, v_x_1141__boxed_2945_, v_x_2942_, v_x_2943_);
    return v_res_2946_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3(
    mut v_00_u03b2_2947_: *mut leanh::LeanObject,
    mut v_x_2948_: *mut leanh::LeanObject,
    mut v_x_2949_: usize,
    mut v_x_2950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2951_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_2948_, v_x_2949_, v_x_2950_);
    return v___x_2951_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_2952_: *mut leanh::LeanObject,
    mut v_x_2953_: *mut leanh::LeanObject,
    mut v_x_2954_: *mut leanh::LeanObject,
    mut v_x_2955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1157__boxed_2956_: usize = 0;
    let mut v_res_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1157__boxed_2956_ = leanh::lean_unbox_usize(v_x_2954_);
    leanh::lean_dec(v_x_2954_);
    v_res_2957_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_2952_, v_x_2953_, v_x_1157__boxed_2956_, v_x_2955_);
    leanh::lean_dec(v_x_2955_);
    leanh::lean_dec_ref(v_x_2953_);
    return v_res_2957_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_2958_: *mut leanh::LeanObject,
    mut v_n_2959_: *mut leanh::LeanObject,
    mut v_k_2960_: *mut leanh::LeanObject,
    mut v_v_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2962_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_n_2959_, v_k_2960_, v_v_2961_);
    return v___x_2962_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_2963_: *mut leanh::LeanObject,
    mut v_depth_2964_: usize,
    mut v_keys_2965_: *mut leanh::LeanObject,
    mut v_vals_2966_: *mut leanh::LeanObject,
    mut v_heq_2967_: *mut leanh::LeanObject,
    mut v_i_2968_: *mut leanh::LeanObject,
    mut v_entries_2969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2970_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_depth_2964_, v_keys_2965_, v_vals_2966_, v_i_2968_, v_entries_2969_);
    return v___x_2970_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_2971_: *mut leanh::LeanObject,
    mut v_depth_2972_: *mut leanh::LeanObject,
    mut v_keys_2973_: *mut leanh::LeanObject,
    mut v_vals_2974_: *mut leanh::LeanObject,
    mut v_heq_2975_: *mut leanh::LeanObject,
    mut v_i_2976_: *mut leanh::LeanObject,
    mut v_entries_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2978_: usize = 0;
    let mut v_res_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2978_ = leanh::lean_unbox_usize(v_depth_2972_);
    leanh::lean_dec(v_depth_2972_);
    v_res_2979_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b2_2971_, v_depth_boxed_2978_, v_keys_2973_, v_vals_2974_, v_heq_2975_, v_i_2976_, v_entries_2977_);
    leanh::lean_dec_ref(v_vals_2974_);
    leanh::lean_dec_ref(v_keys_2973_);
    return v_res_2979_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_2980_: *mut leanh::LeanObject,
    mut v_keys_2981_: *mut leanh::LeanObject,
    mut v_vals_2982_: *mut leanh::LeanObject,
    mut v_heq_2983_: *mut leanh::LeanObject,
    mut v_i_2984_: *mut leanh::LeanObject,
    mut v_k_2985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2986_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_keys_2981_, v_vals_2982_, v_i_2984_, v_k_2985_);
    return v___x_2986_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_2987_: *mut leanh::LeanObject,
    mut v_keys_2988_: *mut leanh::LeanObject,
    mut v_vals_2989_: *mut leanh::LeanObject,
    mut v_heq_2990_: *mut leanh::LeanObject,
    mut v_i_2991_: *mut leanh::LeanObject,
    mut v_k_2992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2993_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(v_00_u03b2_2987_, v_keys_2988_, v_vals_2989_, v_heq_2990_, v_i_2991_, v_k_2992_);
    leanh::lean_dec(v_k_2992_);
    leanh::lean_dec_ref(v_vals_2989_);
    leanh::lean_dec_ref(v_keys_2988_);
    return v_res_2993_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_2994_: *mut leanh::LeanObject,
    mut v_x_2995_: *mut leanh::LeanObject,
    mut v_x_2996_: *mut leanh::LeanObject,
    mut v_x_2997_: *mut leanh::LeanObject,
    mut v_x_2998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2999_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_x_2995_, v_x_2996_, v_x_2997_, v_x_2998_);
    return v___x_2999_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___lam__1(
    mut v___x_3000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3002_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3002_, 0, v___x_3000_);
    return v___x_3002_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___lam__1___boxed(
    mut v___x_3003_: *mut leanh::LeanObject,
    mut v___y_3004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3005_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___lam__1(v___x_3003_);
    return v_res_3005_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msg_3006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3007_ = leanh::lean_box(0);
    v___x_3008_ = lean_panic_fn_borrowed(v___x_3007_, v_msg_3006_);
    return v___x_3008_;
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0_spec__1(
    mut v_newState_3009_: *mut leanh::LeanObject,
    mut v_x_3010_: *mut leanh::LeanObject,
    mut v_x_3011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v_fst_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3021_: u8 = 0;
    let mut v_snd_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3011_) == 0 {
                    return v_x_3010_;
                } else {
                    v_head_3012_ = leanh::lean_ctor_get(v_x_3011_, 0);
                    v_tail_3013_ = leanh::lean_ctor_get(v_x_3011_, 1);
                    v_isSharedCheck_3038_ = (!leanh::lean_is_exclusive(v_x_3011_)) as u8;
                    if v_isSharedCheck_3038_ == 0 {
                        v___x_3015_ = v_x_3011_;
                        v_isShared_3016_ = v_isSharedCheck_3038_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3013_);
                        leanh::lean_inc(v_head_3012_);
                        leanh::lean_dec(v_x_3011_);
                        v___x_3015_ = leanh::lean_box(0);
                        v_isShared_3016_ = v_isSharedCheck_3038_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3017_ = leanh::lean_ctor_get(v_x_3010_, 0);
                v_snd_3018_ = leanh::lean_ctor_get(v_x_3010_, 1);
                v_isSharedCheck_3037_ = (!leanh::lean_is_exclusive(v_x_3010_)) as u8;
                if v_isSharedCheck_3037_ == 0 {
                    v___x_3020_ = v_x_3010_;
                    v_isShared_3021_ = v_isSharedCheck_3037_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3018_);
                    leanh::lean_inc(v_fst_3017_);
                    leanh::lean_dec(v_x_3010_);
                    v___x_3020_ = leanh::lean_box(0);
                    v_isShared_3021_ = v_isSharedCheck_3037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_3022_ = leanh::lean_ctor_get(v_newState_3009_, 1);
                leanh::lean_inc(v_head_3012_);
                if v_isShared_3016_ == 0 {
                    leanh::lean_ctor_set(v___x_3015_, 1, v_fst_3017_);
                    v___x_3024_ = v___x_3015_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_head_3012_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_fst_3017_);
                    v___x_3024_ = v_reuseFailAlloc_3036_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3032_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_3022_, v_head_3012_);
                if leanh::lean_obj_tag(v___x_3032_) == 0 {
                    v___x_3033_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3);
                    v___x_3034_ = l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0_spec__0(v___x_3033_);
                    v___y_3026_ = v___x_3034_;
                    state = 4;
                    continue;
                } else {
                    v_val_3035_ = leanh::lean_ctor_get(v___x_3032_, 0);
                    leanh::lean_inc(v_val_3035_);
                    leanh::lean_dec_ref_known(v___x_3032_, 1);
                    v___y_3026_ = v_val_3035_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3027_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_3018_, v_head_3012_, v___y_3026_);
                if v_isShared_3021_ == 0 {
                    leanh::lean_ctor_set(v___x_3020_, 1, v___x_3027_);
                    leanh::lean_ctor_set(v___x_3020_, 0, v___x_3024_);
                    v___x_3029_ = v___x_3020_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3031_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3031_, 1, v___x_3027_);
                    v___x_3029_ = v_reuseFailAlloc_3031_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_x_3010_ = v___x_3029_;
                v_x_3011_ = v_tail_3013_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_newState_3039_: *mut leanh::LeanObject,
    mut v_x_3040_: *mut leanh::LeanObject,
    mut v_x_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0_spec__1(v_newState_3039_, v_x_3040_, v_x_3041_);
    leanh::lean_dec_ref(v_newState_3039_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___lam__0(
    mut v_oldState_3043_: *mut leanh::LeanObject,
    mut v_newState_3044_: *mut leanh::LeanObject,
    mut v_x_3045_: *mut leanh::LeanObject,
    mut v_s_3046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3047_ = leanh::lean_ctor_get(v_newState_3044_, 0);
    v_fst_3048_ = leanh::lean_ctor_get(v_oldState_3043_, 0);
    v___x_3049_ = l_List_lengthTR___redArg(v_fst_3047_);
    v___x_3050_ = l_List_lengthTR___redArg(v_fst_3048_);
    v___x_3051_ = lean_nat_sub(v___x_3049_, v___x_3050_);
    leanh::lean_dec(v___x_3050_);
    leanh::lean_dec(v___x_3049_);
    v___x_3052_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__0___closed__0;
    leanh::lean_inc(v_fst_3047_);
    v_newEntries_3053_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        leanh::lean_box(0),
        v_fst_3047_,
        v_fst_3047_,
        v___x_3051_,
        v___x_3052_,
    );
    v___x_3054_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0_spec__1(v_newState_3044_, v_s_3046_, v_newEntries_3053_);
    leanh::lean_dec_ref(v_newState_3044_);
    return v___x_3054_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___lam__0___boxed(
    mut v_oldState_3055_: *mut leanh::LeanObject,
    mut v_newState_3056_: *mut leanh::LeanObject,
    mut v_x_3057_: *mut leanh::LeanObject,
    mut v_s_3058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3059_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___lam__0(v_oldState_3055_, v_newState_3056_, v_x_3057_, v_s_3058_);
    leanh::lean_dec(v_x_3057_);
    leanh::lean_dec_ref(v_oldState_3055_);
    return v_res_3059_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3061_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3061_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3062_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__1);
    v___x_3063_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3063_, 0, v___x_3062_);
    return v___x_3063_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3064_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__2);
    v___x_3065_ = leanh::lean_box(0);
    v___x_3066_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3066_, 0, v___x_3065_);
    leanh::lean_ctor_set(v___x_3066_, 1, v___x_3064_);
    return v___x_3066_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3067_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__3);
    v___f_3068_ = leanh::lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_3068_, 0, v___x_3067_);
    return v___f_3068_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0()
-> *mut leanh::LeanObject {
    let mut v___f_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut v_a_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3087_: u8 = 0;
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3072_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__4_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__4);
                v___x_3073_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___closed__5;
                v___x_3074_ = leanh::lean_box(0);
                v___x_3075_ =
                    l_Lean_registerEnvExtension___redArg(v___f_3072_, v___x_3073_, v___x_3074_);
                if leanh::lean_obj_tag(v___x_3075_) == 0 {
                    v_a_3076_ = leanh::lean_ctor_get(v___x_3075_, 0);
                    v_isSharedCheck_3083_ = (!leanh::lean_is_exclusive(v___x_3075_)) as u8;
                    if v_isSharedCheck_3083_ == 0 {
                        v___x_3078_ = v___x_3075_;
                        v_isShared_3079_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3076_);
                        leanh::lean_dec(v___x_3075_);
                        v___x_3078_ = leanh::lean_box(0);
                        v_isShared_3079_ = v_isSharedCheck_3083_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3084_ = leanh::lean_ctor_get(v___x_3075_, 0);
                    v_isSharedCheck_3091_ = (!leanh::lean_is_exclusive(v___x_3075_)) as u8;
                    if v_isSharedCheck_3091_ == 0 {
                        v___x_3086_ = v___x_3075_;
                        v_isShared_3087_ = v_isSharedCheck_3091_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3084_);
                        leanh::lean_dec(v___x_3075_);
                        v___x_3086_ = leanh::lean_box(0);
                        v_isShared_3087_ = v_isSharedCheck_3091_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3079_ == 0 {
                    v___x_3081_ = v___x_3078_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
                    v___x_3081_ = v_reuseFailAlloc_3082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3081_;
            }
            3 => {
                if v_isShared_3087_ == 0 {
                    v___x_3089_ = v___x_3086_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3090_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
                    v___x_3089_ = v_reuseFailAlloc_3090_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0___boxed(
    mut v_a_3092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3093_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0();
    return v_res_3093_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3095_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2__spec__0();
    return v___x_3095_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2____boxed(
    mut v_a_3096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3097_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2_();
    return v_res_3097_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0(
    mut v_type_3101_: *mut leanh::LeanObject,
    mut v___y_3102_: *mut leanh::LeanObject,
    mut v___y_3103_: *mut leanh::LeanObject,
    mut v___y_3104_: *mut leanh::LeanObject,
    mut v___y_3105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: u8 = 0;
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: u8 = 0;
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v_typeName_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: u8 = 0;
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: u8 = 0;
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v_a_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3185_: u8 = 0;
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_type_3101_);
                v___x_3107_ = l_Lean_Meta_isProp(
                    v_type_3101_,
                    v___y_3102_,
                    v___y_3103_,
                    v___y_3104_,
                    v___y_3105_,
                );
                if leanh::lean_obj_tag(v___x_3107_) == 0 {
                    v_a_3108_ = leanh::lean_ctor_get(v___x_3107_, 0);
                    leanh::lean_inc(v_a_3108_);
                    v___x_3109_ = (leanh::lean_unbox(v_a_3108_) as u8);
                    leanh::lean_dec(v_a_3108_);
                    if v___x_3109_ == 0 {
                        leanh::lean_dec_ref_known(v___x_3107_, 1);
                        leanh::lean_inc_ref(v_type_3101_);
                        v___x_3110_ = l_Lean_Meta_isTypeFormerType(
                            v_type_3101_,
                            v___y_3102_,
                            v___y_3103_,
                            v___y_3104_,
                            v___y_3105_,
                        );
                        if leanh::lean_obj_tag(v___x_3110_) == 0 {
                            v_a_3111_ = leanh::lean_ctor_get(v___x_3110_, 0);
                            leanh::lean_inc(v_a_3111_);
                            v___x_3112_ = (leanh::lean_unbox(v_a_3111_) as u8);
                            if v___x_3112_ == 0 {
                                leanh::lean_dec_ref_known(v___x_3110_, 1);
                                v___x_3113_ = l_Lean_Meta_whnfD(
                                    v_type_3101_,
                                    v___y_3102_,
                                    v___y_3103_,
                                    v___y_3104_,
                                    v___y_3105_,
                                );
                                if leanh::lean_obj_tag(v___x_3113_) == 0 {
                                    v_a_3114_ = leanh::lean_ctor_get(v___x_3113_, 0);
                                    v_isSharedCheck_3181_ =
                                        (!leanh::lean_is_exclusive(v___x_3113_)) as u8;
                                    if v_isSharedCheck_3181_ == 0 {
                                        v___x_3116_ = v___x_3113_;
                                        v_isShared_3117_ = v_isSharedCheck_3181_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3114_);
                                        leanh::lean_dec(v___x_3113_);
                                        v___x_3116_ = leanh::lean_box(0);
                                        v_isShared_3117_ = v_isSharedCheck_3181_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_3111_);
                                    v_a_3182_ = leanh::lean_ctor_get(v___x_3113_, 0);
                                    v_isSharedCheck_3189_ =
                                        (!leanh::lean_is_exclusive(v___x_3113_)) as u8;
                                    if v_isSharedCheck_3189_ == 0 {
                                        v___x_3184_ = v___x_3113_;
                                        v_isShared_3185_ = v_isSharedCheck_3189_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3182_);
                                        leanh::lean_dec(v___x_3113_);
                                        v___x_3184_ = leanh::lean_box(0);
                                        v_isShared_3185_ = v_isSharedCheck_3189_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_a_3111_);
                                leanh::lean_dec_ref(v_type_3101_);
                                return v___x_3110_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_type_3101_);
                            return v___x_3110_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_type_3101_);
                        return v___x_3107_;
                    }
                } else {
                    leanh::lean_dec_ref(v_type_3101_);
                    return v___x_3107_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3114_) == 11 {
                    v_typeName_3118_ = leanh::lean_ctor_get(v_a_3114_, 0);
                    leanh::lean_inc(v_typeName_3118_);
                    if leanh::lean_obj_tag(v_typeName_3118_) == 1 {
                        v_pre_3119_ = leanh::lean_ctor_get(v_typeName_3118_, 0);
                        if leanh::lean_obj_tag(v_pre_3119_) == 0 {
                            v_idx_3120_ = leanh::lean_ctor_get(v_a_3114_, 1);
                            leanh::lean_inc(v_idx_3120_);
                            v_struct_3121_ = leanh::lean_ctor_get(v_a_3114_, 2);
                            leanh::lean_inc_ref(v_struct_3121_);
                            leanh::lean_dec_ref_known(v_a_3114_, 3);
                            v_str_3122_ = leanh::lean_ctor_get(v_typeName_3118_, 1);
                            leanh::lean_inc_ref(v_str_3122_);
                            leanh::lean_dec_ref_known(v_typeName_3118_, 2);
                            v___x_3123_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__0;
                            v___x_3124_ = lean_string_dec_eq(v_str_3122_, v___x_3123_);
                            leanh::lean_dec_ref(v_str_3122_);
                            if v___x_3124_ == 0 {
                                leanh::lean_dec_ref(v_struct_3121_);
                                leanh::lean_dec(v_idx_3120_);
                                if v_isShared_3117_ == 0 {
                                    leanh::lean_ctor_set(v___x_3116_, 0, v_a_3111_);
                                    v___x_3126_ = v___x_3116_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3127_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3127_,
                                        0,
                                        v_a_3111_,
                                    );
                                    v___x_3126_ = v_reuseFailAlloc_3127_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_3128_ = leanh::lean_unsigned_to_nat(0);
                                v___x_3129_ = lean_nat_dec_eq(v_idx_3120_, v___x_3128_);
                                leanh::lean_dec(v_idx_3120_);
                                if v___x_3129_ == 0 {
                                    leanh::lean_dec_ref(v_struct_3121_);
                                    if v_isShared_3117_ == 0 {
                                        leanh::lean_ctor_set(v___x_3116_, 0, v_a_3111_);
                                        v___x_3131_ = v___x_3116_;
                                        state = 3;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3132_ =
                                            leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3132_,
                                            0,
                                            v_a_3111_,
                                        );
                                        v___x_3131_ = v_reuseFailAlloc_3132_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    if leanh::lean_obj_tag(v_struct_3121_) == 5 {
                                        v_fn_3133_ = leanh::lean_ctor_get(v_struct_3121_, 0);
                                        leanh::lean_inc_ref(v_fn_3133_);
                                        leanh::lean_dec_ref_known(v_struct_3121_, 2);
                                        if leanh::lean_obj_tag(v_fn_3133_) == 4 {
                                            v_declName_3134_ =
                                                leanh::lean_ctor_get(v_fn_3133_, 0);
                                            leanh::lean_inc(v_declName_3134_);
                                            if leanh::lean_obj_tag(v_declName_3134_) == 1 {
                                                v_pre_3135_ = leanh::lean_ctor_get(
                                                    v_declName_3134_,
                                                    0,
                                                );
                                                leanh::lean_inc(v_pre_3135_);
                                                if leanh::lean_obj_tag(v_pre_3135_) == 1 {
                                                    v_pre_3136_ =
                                                        leanh::lean_ctor_get(v_pre_3135_, 0);
                                                    if leanh::lean_obj_tag(v_pre_3136_) == 0
                                                    {
                                                        v_us_3137_ = leanh::lean_ctor_get(
                                                            v_fn_3133_, 1,
                                                        );
                                                        leanh::lean_inc(v_us_3137_);
                                                        leanh::lean_dec_ref_known(
                                                            v_fn_3133_, 2,
                                                        );
                                                        v_str_3138_ = leanh::lean_ctor_get(
                                                            v_declName_3134_,
                                                            1,
                                                        );
                                                        leanh::lean_inc_ref(v_str_3138_);
                                                        leanh::lean_dec_ref_known(
                                                            v_declName_3134_,
                                                            2,
                                                        );
                                                        v_str_3139_ = leanh::lean_ctor_get(
                                                            v_pre_3135_,
                                                            1,
                                                        );
                                                        leanh::lean_inc_ref(v_str_3139_);
                                                        leanh::lean_dec_ref_known(
                                                            v_pre_3135_,
                                                            2,
                                                        );
                                                        v___x_3140_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__1;
                                                        v___x_3141_ = lean_string_dec_eq(
                                                            v_str_3139_,
                                                            v___x_3140_,
                                                        );
                                                        leanh::lean_dec_ref(v_str_3139_);
                                                        if v___x_3141_ == 0 {
                                                            leanh::lean_dec_ref(v_str_3138_);
                                                            leanh::lean_dec(v_us_3137_);
                                                            if v_isShared_3117_ == 0 {
                                                                leanh::lean_ctor_set(
                                                                    v___x_3116_,
                                                                    0,
                                                                    v_a_3111_,
                                                                );
                                                                v___x_3143_ = v___x_3116_;
                                                                state = 4;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_3144_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v_reuseFailAlloc_3144_,
                                                                    0,
                                                                    v_a_3111_,
                                                                );
                                                                v___x_3143_ =
                                                                    v_reuseFailAlloc_3144_;
                                                                state = 4;
                                                                continue;
                                                            }
                                                        } else {
                                                            v___x_3145_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___closed__2;
                                                            v___x_3146_ = lean_string_dec_eq(
                                                                v_str_3138_,
                                                                v___x_3145_,
                                                            );
                                                            leanh::lean_dec_ref(v_str_3138_);
                                                            if v___x_3146_ == 0 {
                                                                leanh::lean_dec(v_us_3137_);
                                                                if v_isShared_3117_ == 0 {
                                                                    leanh::lean_ctor_set(
                                                                        v___x_3116_,
                                                                        0,
                                                                        v_a_3111_,
                                                                    );
                                                                    v___x_3148_ = v___x_3116_;
                                                                    state = 5;
                                                                    continue;
                                                                } else {
                                                                    v_reuseFailAlloc_3149_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v_reuseFailAlloc_3149_,
                                                                        0,
                                                                        v_a_3111_,
                                                                    );
                                                                    v___x_3148_ =
                                                                        v_reuseFailAlloc_3149_;
                                                                    state = 5;
                                                                    continue;
                                                                }
                                                            } else {
                                                                if leanh::lean_obj_tag(
                                                                    v_us_3137_,
                                                                ) == 0
                                                                {
                                                                    leanh::lean_dec(
                                                                        v_a_3111_,
                                                                    );
                                                                    v___x_3150_ =
                                                                        leanh::lean_box(
                                                                            (v___x_3146_) as usize,
                                                                        );
                                                                    if v_isShared_3117_ == 0 {
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3116_,
                                                                            0,
                                                                            v___x_3150_,
                                                                        );
                                                                        v___x_3152_ = v___x_3116_;
                                                                        state = 6;
                                                                        continue;
                                                                    } else {
                                                                        v_reuseFailAlloc_3153_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v_reuseFailAlloc_3153_,
                                                                            0,
                                                                            v___x_3150_,
                                                                        );
                                                                        v___x_3152_ =
                                                                            v_reuseFailAlloc_3153_;
                                                                        state = 6;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v_us_3137_,
                                                                    );
                                                                    if v_isShared_3117_ == 0 {
                                                                        leanh::lean_ctor_set(
                                                                            v___x_3116_,
                                                                            0,
                                                                            v_a_3111_,
                                                                        );
                                                                        v___x_3155_ = v___x_3116_;
                                                                        state = 7;
                                                                        continue;
                                                                    } else {
                                                                        v_reuseFailAlloc_3156_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v_reuseFailAlloc_3156_,
                                                                            0,
                                                                            v_a_3111_,
                                                                        );
                                                                        v___x_3155_ =
                                                                            v_reuseFailAlloc_3156_;
                                                                        state = 7;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref_known(
                                                            v_pre_3135_,
                                                            2,
                                                        );
                                                        leanh::lean_dec_ref_known(
                                                            v_declName_3134_,
                                                            2,
                                                        );
                                                        leanh::lean_dec_ref_known(
                                                            v_fn_3133_, 2,
                                                        );
                                                        if v_isShared_3117_ == 0 {
                                                            leanh::lean_ctor_set(
                                                                v___x_3116_,
                                                                0,
                                                                v_a_3111_,
                                                            );
                                                            v___x_3158_ = v___x_3116_;
                                                            state = 8;
                                                            continue;
                                                        } else {
                                                            v_reuseFailAlloc_3159_ =
                                                                leanh::lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v_reuseFailAlloc_3159_,
                                                                0,
                                                                v_a_3111_,
                                                            );
                                                            v___x_3158_ = v_reuseFailAlloc_3159_;
                                                            state = 8;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref_known(
                                                        v_declName_3134_,
                                                        2,
                                                    );
                                                    leanh::lean_dec(v_pre_3135_);
                                                    leanh::lean_dec_ref_known(v_fn_3133_, 2);
                                                    if v_isShared_3117_ == 0 {
                                                        leanh::lean_ctor_set(
                                                            v___x_3116_,
                                                            0,
                                                            v_a_3111_,
                                                        );
                                                        v___x_3161_ = v___x_3116_;
                                                        state = 9;
                                                        continue;
                                                    } else {
                                                        v_reuseFailAlloc_3162_ =
                                                            leanh::lean_alloc_ctor(
                                                                0,
                                                                1,
                                                                (0) as u32,
                                                            );
                                                        leanh::lean_ctor_set(
                                                            v_reuseFailAlloc_3162_,
                                                            0,
                                                            v_a_3111_,
                                                        );
                                                        v___x_3161_ = v_reuseFailAlloc_3162_;
                                                        state = 9;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec(v_declName_3134_);
                                                leanh::lean_dec_ref_known(v_fn_3133_, 2);
                                                if v_isShared_3117_ == 0 {
                                                    leanh::lean_ctor_set(
                                                        v___x_3116_,
                                                        0,
                                                        v_a_3111_,
                                                    );
                                                    v___x_3164_ = v___x_3116_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3165_ =
                                                        leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3165_,
                                                        0,
                                                        v_a_3111_,
                                                    );
                                                    v___x_3164_ = v_reuseFailAlloc_3165_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_fn_3133_);
                                            if v_isShared_3117_ == 0 {
                                                leanh::lean_ctor_set(
                                                    v___x_3116_,
                                                    0,
                                                    v_a_3111_,
                                                );
                                                v___x_3167_ = v___x_3116_;
                                                state = 11;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3168_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_3168_,
                                                    0,
                                                    v_a_3111_,
                                                );
                                                v___x_3167_ = v_reuseFailAlloc_3168_;
                                                state = 11;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_struct_3121_);
                                        if v_isShared_3117_ == 0 {
                                            leanh::lean_ctor_set(v___x_3116_, 0, v_a_3111_);
                                            v___x_3170_ = v___x_3116_;
                                            state = 12;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3171_ =
                                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3171_,
                                                0,
                                                v_a_3111_,
                                            );
                                            v___x_3170_ = v_reuseFailAlloc_3171_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_typeName_3118_, 2);
                            leanh::lean_dec_ref_known(v_a_3114_, 3);
                            if v_isShared_3117_ == 0 {
                                leanh::lean_ctor_set(v___x_3116_, 0, v_a_3111_);
                                v___x_3173_ = v___x_3116_;
                                state = 13;
                                continue;
                            } else {
                                v_reuseFailAlloc_3174_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3111_);
                                v___x_3173_ = v_reuseFailAlloc_3174_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_typeName_3118_);
                        leanh::lean_dec_ref_known(v_a_3114_, 3);
                        if v_isShared_3117_ == 0 {
                            leanh::lean_ctor_set(v___x_3116_, 0, v_a_3111_);
                            v___x_3176_ = v___x_3116_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3177_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3111_);
                            v___x_3176_ = v_reuseFailAlloc_3177_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3114_);
                    if v_isShared_3117_ == 0 {
                        leanh::lean_ctor_set(v___x_3116_, 0, v_a_3111_);
                        v___x_3179_ = v___x_3116_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3111_);
                        v___x_3179_ = v_reuseFailAlloc_3180_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3126_;
            }
            3 => {
                return v___x_3131_;
            }
            4 => {
                return v___x_3143_;
            }
            5 => {
                return v___x_3148_;
            }
            6 => {
                return v___x_3152_;
            }
            7 => {
                return v___x_3155_;
            }
            8 => {
                return v___x_3158_;
            }
            9 => {
                return v___x_3161_;
            }
            10 => {
                return v___x_3164_;
            }
            11 => {
                return v___x_3167_;
            }
            12 => {
                return v___x_3170_;
            }
            13 => {
                return v___x_3173_;
            }
            14 => {
                return v___x_3176_;
            }
            15 => {
                return v___x_3179_;
            }
            16 => {
                if v_isShared_3185_ == 0 {
                    v___x_3187_ = v___x_3184_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3188_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
                    v___x_3187_ = v_reuseFailAlloc_3188_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0___boxed(
    mut v_type_3190_: *mut leanh::LeanObject,
    mut v___y_3191_: *mut leanh::LeanObject,
    mut v___y_3192_: *mut leanh::LeanObject,
    mut v___y_3193_: *mut leanh::LeanObject,
    mut v___y_3194_: *mut leanh::LeanObject,
    mut v___y_3195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3196_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___lam__0(
        v_type_3190_,
        v___y_3191_,
        v___y_3192_,
        v___y_3193_,
        v___y_3194_,
    );
    leanh::lean_dec(v___y_3194_);
    leanh::lean_dec_ref(v___y_3193_);
    leanh::lean_dec(v___y_3192_);
    leanh::lean_dec_ref(v___y_3191_);
    return v_res_3196_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(
    mut v_declName_3198_: *mut leanh::LeanObject,
    mut v_a_3199_: *mut leanh::LeanObject,
    mut v_a_3200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_irrelevantType_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_irrelevantType_3202_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___closed__0;
    v___x_3203_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt;
    v___x_3204_ = l_Lean_Compiler_LCNF_Irrelevant_hasTrivialStructure_x3f(
        v___x_3203_,
        v_irrelevantType_3202_,
        v_declName_3198_,
        v_a_3199_,
        v_a_3200_,
    );
    return v___x_3204_;
}
pub unsafe fn l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f___boxed(
    mut v_declName_3205_: *mut leanh::LeanObject,
    mut v_a_3206_: *mut leanh::LeanObject,
    mut v_a_3207_: *mut leanh::LeanObject,
    mut v_a_3208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3209_ =
        l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(v_declName_3205_, v_a_3206_, v_a_3207_);
    leanh::lean_dec(v_a_3207_);
    leanh::lean_dec_ref(v_a_3206_);
    return v_res_3209_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__0(
    mut v_msg_3211_: *mut leanh::LeanObject,
    mut v___y_3212_: *mut leanh::LeanObject,
    mut v___y_3213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6890__overap_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3215_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__0___closed__0;
    v___x_6890__overap_3216_ = lean_panic_fn_borrowed(v___f_3215_, v_msg_3211_);
    leanh::lean_inc(v___y_3213_);
    leanh::lean_inc_ref(v___y_3212_);
    v___x_3217_ = leanh::lean_apply_3(
        v___x_6890__overap_3216_,
        v___y_3212_,
        v___y_3213_,
        leanh::lean_box(0),
    );
    return v___x_3217_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__0___boxed(
    mut v_msg_3218_: *mut leanh::LeanObject,
    mut v___y_3219_: *mut leanh::LeanObject,
    mut v___y_3220_: *mut leanh::LeanObject,
    mut v___y_3221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3222_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__0(v_msg_3218_, v___y_3219_, v___y_3220_);
    leanh::lean_dec(v___y_3220_);
    leanh::lean_dec_ref(v___y_3219_);
    return v_res_3222_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___redArg___lam__0(
    mut v_k_3223_: *mut leanh::LeanObject,
    mut v_b_3224_: *mut leanh::LeanObject,
    mut v_c_3225_: *mut leanh::LeanObject,
    mut v___y_3226_: *mut leanh::LeanObject,
    mut v___y_3227_: *mut leanh::LeanObject,
    mut v___y_3228_: *mut leanh::LeanObject,
    mut v___y_3229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3229_);
    leanh::lean_inc_ref(v___y_3228_);
    leanh::lean_inc(v___y_3227_);
    leanh::lean_inc_ref(v___y_3226_);
    v___x_3231_ = leanh::lean_apply_7(
        v_k_3223_,
        v_b_3224_,
        v_c_3225_,
        v___y_3226_,
        v___y_3227_,
        v___y_3228_,
        v___y_3229_,
        leanh::lean_box(0),
    );
    return v___x_3231_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___redArg___lam__0___boxed(
    mut v_k_3232_: *mut leanh::LeanObject,
    mut v_b_3233_: *mut leanh::LeanObject,
    mut v_c_3234_: *mut leanh::LeanObject,
    mut v___y_3235_: *mut leanh::LeanObject,
    mut v___y_3236_: *mut leanh::LeanObject,
    mut v___y_3237_: *mut leanh::LeanObject,
    mut v___y_3238_: *mut leanh::LeanObject,
    mut v___y_3239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3240_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___redArg___lam__0(v_k_3232_, v_b_3233_, v_c_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
    leanh::lean_dec(v___y_3238_);
    leanh::lean_dec_ref(v___y_3237_);
    leanh::lean_dec(v___y_3236_);
    leanh::lean_dec_ref(v___y_3235_);
    return v_res_3240_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___redArg(
    mut v_type_3241_: *mut leanh::LeanObject,
    mut v_k_3242_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3243_: u8,
    mut v___y_3244_: *mut leanh::LeanObject,
    mut v___y_3245_: *mut leanh::LeanObject,
    mut v___y_3246_: *mut leanh::LeanObject,
    mut v___y_3247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: u8 = 0;
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3256_: u8 = 0;
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3260_: u8 = 0;
    let mut v_a_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3264_: u8 = 0;
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3249_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_3249_, 0, v_k_3242_);
                v___x_3250_ = 0;
                v___x_3251_ = leanh::lean_box(0);
                v___x_3252_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        leanh::lean_box(0),
                        v___x_3250_,
                        v___x_3251_,
                        v_type_3241_,
                        v___f_3249_,
                        v_cleanupAnnotations_3243_,
                        v___x_3250_,
                        v___y_3244_,
                        v___y_3245_,
                        v___y_3246_,
                        v___y_3247_,
                    );
                if leanh::lean_obj_tag(v___x_3252_) == 0 {
                    v_a_3253_ = leanh::lean_ctor_get(v___x_3252_, 0);
                    v_isSharedCheck_3260_ = (!leanh::lean_is_exclusive(v___x_3252_)) as u8;
                    if v_isSharedCheck_3260_ == 0 {
                        v___x_3255_ = v___x_3252_;
                        v_isShared_3256_ = v_isSharedCheck_3260_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3253_);
                        leanh::lean_dec(v___x_3252_);
                        v___x_3255_ = leanh::lean_box(0);
                        v_isShared_3256_ = v_isSharedCheck_3260_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3261_ = leanh::lean_ctor_get(v___x_3252_, 0);
                    v_isSharedCheck_3268_ = (!leanh::lean_is_exclusive(v___x_3252_)) as u8;
                    if v_isSharedCheck_3268_ == 0 {
                        v___x_3263_ = v___x_3252_;
                        v_isShared_3264_ = v_isSharedCheck_3268_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3261_);
                        leanh::lean_dec(v___x_3252_);
                        v___x_3263_ = leanh::lean_box(0);
                        v_isShared_3264_ = v_isSharedCheck_3268_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3256_ == 0 {
                    v___x_3258_ = v___x_3255_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3259_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3253_);
                    v___x_3258_ = v_reuseFailAlloc_3259_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3258_;
            }
            3 => {
                if v_isShared_3264_ == 0 {
                    v___x_3266_ = v___x_3263_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3267_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
                    v___x_3266_ = v_reuseFailAlloc_3267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___redArg___boxed(
    mut v_type_3269_: *mut leanh::LeanObject,
    mut v_k_3270_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3271_: *mut leanh::LeanObject,
    mut v___y_3272_: *mut leanh::LeanObject,
    mut v___y_3273_: *mut leanh::LeanObject,
    mut v___y_3274_: *mut leanh::LeanObject,
    mut v___y_3275_: *mut leanh::LeanObject,
    mut v___y_3276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3277_: u8 = 0;
    let mut v_res_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3277_ = (leanh::lean_unbox(v_cleanupAnnotations_3271_) as u8);
    v_res_3278_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___redArg(v_type_3269_, v_k_3270_, v_cleanupAnnotations_boxed_3277_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
    leanh::lean_dec(v___y_3275_);
    leanh::lean_dec_ref(v___y_3274_);
    leanh::lean_dec(v___y_3273_);
    leanh::lean_dec_ref(v___y_3272_);
    return v_res_3278_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2(
    mut v_00_u03b1_3279_: *mut leanh::LeanObject,
    mut v_type_3280_: *mut leanh::LeanObject,
    mut v_k_3281_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3282_: u8,
    mut v___y_3283_: *mut leanh::LeanObject,
    mut v___y_3284_: *mut leanh::LeanObject,
    mut v___y_3285_: *mut leanh::LeanObject,
    mut v___y_3286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3288_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___redArg(v_type_3280_, v_k_3281_, v_cleanupAnnotations_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
    return v___x_3288_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___boxed(
    mut v_00_u03b1_3289_: *mut leanh::LeanObject,
    mut v_type_3290_: *mut leanh::LeanObject,
    mut v_k_3291_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3292_: *mut leanh::LeanObject,
    mut v___y_3293_: *mut leanh::LeanObject,
    mut v___y_3294_: *mut leanh::LeanObject,
    mut v___y_3295_: *mut leanh::LeanObject,
    mut v___y_3296_: *mut leanh::LeanObject,
    mut v___y_3297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3298_: u8 = 0;
    let mut v_res_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3298_ = (leanh::lean_unbox(v_cleanupAnnotations_3292_) as u8);
    v_res_3299_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2(v_00_u03b1_3289_, v_type_3290_, v_k_3291_, v_cleanupAnnotations_boxed_3298_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
    leanh::lean_dec(v___y_3296_);
    leanh::lean_dec_ref(v___y_3295_);
    leanh::lean_dec(v___y_3294_);
    leanh::lean_dec_ref(v___y_3293_);
    return v_res_3299_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___redArg(
    mut v_a_3303_: *mut leanh::LeanObject,
    mut v_b_3304_: *mut leanh::LeanObject,
    mut v___y_3305_: *mut leanh::LeanObject,
    mut v___y_3306_: *mut leanh::LeanObject,
    mut v___y_3307_: *mut leanh::LeanObject,
    mut v___y_3308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v___x_3316_: u8 = 0;
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3328_: u8 = 0;
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: u8 = 0;
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3344_: u8 = 0;
    let mut v_a_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3348_: u8 = 0;
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3352_: u8 = 0;
    let mut v_a_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3360_: u8 = 0;
    let mut v_a_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3364_: u8 = 0;
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3368_: u8 = 0;
    let mut v_isSharedCheck_3369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3310_ = leanh::lean_ctor_get(v_a_3303_, 0);
                v_start_3311_ = leanh::lean_ctor_get(v_a_3303_, 1);
                v_stop_3312_ = leanh::lean_ctor_get(v_a_3303_, 2);
                v_isSharedCheck_3369_ = (!leanh::lean_is_exclusive(v_a_3303_)) as u8;
                if v_isSharedCheck_3369_ == 0 {
                    v___x_3314_ = v_a_3303_;
                    v_isShared_3315_ = v_isSharedCheck_3369_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_3312_);
                    leanh::lean_inc(v_start_3311_);
                    leanh::lean_inc(v_array_3310_);
                    leanh::lean_dec(v_a_3303_);
                    v___x_3314_ = leanh::lean_box(0);
                    v_isShared_3315_ = v_isSharedCheck_3369_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3316_ = lean_nat_dec_lt(v_start_3311_, v_stop_3312_);
                if v___x_3316_ == 0 {
                    leanh::lean_del_object(v___x_3314_);
                    leanh::lean_dec(v_stop_3312_);
                    leanh::lean_dec(v_start_3311_);
                    leanh::lean_dec_ref(v_array_3310_);
                    v___x_3317_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3317_, 0, v_b_3304_);
                    return v___x_3317_;
                } else {
                    leanh::lean_dec_ref(v_b_3304_);
                    v___x_3318_ = lean_array_fget_borrowed(v_array_3310_, v_start_3311_);
                    v___x_3319_ = l_Lean_Expr_fvarId_x21(v___x_3318_);
                    v___x_3320_ = l_Lean_FVarId_getType___redArg(
                        v___x_3319_,
                        v___y_3305_,
                        v___y_3307_,
                        v___y_3308_,
                    );
                    if leanh::lean_obj_tag(v___x_3320_) == 0 {
                        v_a_3321_ = leanh::lean_ctor_get(v___x_3320_, 0);
                        leanh::lean_inc(v_a_3321_);
                        leanh::lean_dec_ref_known(v___x_3320_, 1);
                        v___x_3322_ = l_Lean_Compiler_LCNF_toLCNFType(
                            v_a_3321_,
                            v___y_3305_,
                            v___y_3306_,
                            v___y_3307_,
                            v___y_3308_,
                        );
                        if leanh::lean_obj_tag(v___x_3322_) == 0 {
                            v_a_3323_ = leanh::lean_ctor_get(v___x_3322_, 0);
                            leanh::lean_inc(v_a_3323_);
                            leanh::lean_dec_ref_known(v___x_3322_, 1);
                            v___x_3324_ = l_Lean_Compiler_LCNF_toMonoType(
                                v_a_3323_,
                                v___y_3307_,
                                v___y_3308_,
                            );
                            if leanh::lean_obj_tag(v___x_3324_) == 0 {
                                v_a_3325_ = leanh::lean_ctor_get(v___x_3324_, 0);
                                v_isSharedCheck_3344_ =
                                    (!leanh::lean_is_exclusive(v___x_3324_)) as u8;
                                if v_isSharedCheck_3344_ == 0 {
                                    v___x_3327_ = v___x_3324_;
                                    v_isShared_3328_ = v_isSharedCheck_3344_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3325_);
                                    leanh::lean_dec(v___x_3324_);
                                    v___x_3327_ = leanh::lean_box(0);
                                    v_isShared_3328_ = v_isSharedCheck_3344_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_3314_);
                                leanh::lean_dec(v_stop_3312_);
                                leanh::lean_dec(v_start_3311_);
                                leanh::lean_dec_ref(v_array_3310_);
                                v_a_3345_ = leanh::lean_ctor_get(v___x_3324_, 0);
                                v_isSharedCheck_3352_ =
                                    (!leanh::lean_is_exclusive(v___x_3324_)) as u8;
                                if v_isSharedCheck_3352_ == 0 {
                                    v___x_3347_ = v___x_3324_;
                                    v_isShared_3348_ = v_isSharedCheck_3352_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3345_);
                                    leanh::lean_dec(v___x_3324_);
                                    v___x_3347_ = leanh::lean_box(0);
                                    v_isShared_3348_ = v_isSharedCheck_3352_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_3314_);
                            leanh::lean_dec(v_stop_3312_);
                            leanh::lean_dec(v_start_3311_);
                            leanh::lean_dec_ref(v_array_3310_);
                            v_a_3353_ = leanh::lean_ctor_get(v___x_3322_, 0);
                            v_isSharedCheck_3360_ =
                                (!leanh::lean_is_exclusive(v___x_3322_)) as u8;
                            if v_isSharedCheck_3360_ == 0 {
                                v___x_3355_ = v___x_3322_;
                                v_isShared_3356_ = v_isSharedCheck_3360_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3353_);
                                leanh::lean_dec(v___x_3322_);
                                v___x_3355_ = leanh::lean_box(0);
                                v_isShared_3356_ = v_isSharedCheck_3360_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_3314_);
                        leanh::lean_dec(v_stop_3312_);
                        leanh::lean_dec(v_start_3311_);
                        leanh::lean_dec_ref(v_array_3310_);
                        v_a_3361_ = leanh::lean_ctor_get(v___x_3320_, 0);
                        v_isSharedCheck_3368_ =
                            (!leanh::lean_is_exclusive(v___x_3320_)) as u8;
                        if v_isSharedCheck_3368_ == 0 {
                            v___x_3363_ = v___x_3320_;
                            v_isShared_3364_ = v_isSharedCheck_3368_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3361_);
                            leanh::lean_dec(v___x_3320_);
                            v___x_3363_ = leanh::lean_box(0);
                            v_isShared_3364_ = v_isSharedCheck_3368_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3329_ = leanh::lean_box(0);
                v___x_3330_ = l_Lean_Expr_isErased(v_a_3325_);
                leanh::lean_dec(v_a_3325_);
                if v___x_3330_ == 0 {
                    leanh::lean_del_object(v___x_3314_);
                    leanh::lean_dec(v_stop_3312_);
                    leanh::lean_dec(v_start_3311_);
                    leanh::lean_dec_ref(v_array_3310_);
                    v___x_3331_ = leanh::lean_box((v___x_3316_) as usize);
                    v___x_3332_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3332_, 0, v___x_3331_);
                    v___x_3333_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3333_, 0, v___x_3332_);
                    leanh::lean_ctor_set(v___x_3333_, 1, v___x_3329_);
                    if v_isShared_3328_ == 0 {
                        leanh::lean_ctor_set(v___x_3327_, 0, v___x_3333_);
                        v___x_3335_ = v___x_3327_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3336_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
                        v___x_3335_ = v_reuseFailAlloc_3336_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3327_);
                    v___x_3337_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___redArg___closed__0;
                    v___x_3338_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3339_ = lean_nat_add(v_start_3311_, v___x_3338_);
                    leanh::lean_dec(v_start_3311_);
                    if v_isShared_3315_ == 0 {
                        leanh::lean_ctor_set(v___x_3314_, 1, v___x_3339_);
                        v___x_3341_ = v___x_3314_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3343_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_array_3310_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3343_, 1, v___x_3339_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3343_, 2, v_stop_3312_);
                        v___x_3341_ = v_reuseFailAlloc_3343_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3335_;
            }
            4 => {
                v_a_3303_ = v___x_3341_;
                v_b_3304_ = v___x_3337_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_3348_ == 0 {
                    v___x_3350_ = v___x_3347_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
                    v___x_3350_ = v_reuseFailAlloc_3351_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3350_;
            }
            7 => {
                if v_isShared_3356_ == 0 {
                    v___x_3358_ = v___x_3355_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3359_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
                    v___x_3358_ = v_reuseFailAlloc_3359_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3358_;
            }
            9 => {
                if v_isShared_3364_ == 0 {
                    v___x_3366_ = v___x_3363_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3367_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
                    v___x_3366_ = v_reuseFailAlloc_3367_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3366_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___redArg___boxed(
    mut v_a_3370_: *mut leanh::LeanObject,
    mut v_b_3371_: *mut leanh::LeanObject,
    mut v___y_3372_: *mut leanh::LeanObject,
    mut v___y_3373_: *mut leanh::LeanObject,
    mut v___y_3374_: *mut leanh::LeanObject,
    mut v___y_3375_: *mut leanh::LeanObject,
    mut v___y_3376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3377_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___redArg(v_a_3370_, v_b_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
    leanh::lean_dec(v___y_3375_);
    leanh::lean_dec_ref(v___y_3374_);
    leanh::lean_dec(v___y_3373_);
    leanh::lean_dec_ref(v___y_3372_);
    return v_res_3377_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___lam__0(
    mut v___x_3378_: u8,
    mut v_numParams_3379_: *mut leanh::LeanObject,
    mut v___x_3380_: *mut leanh::LeanObject,
    mut v_params_3381_: *mut leanh::LeanObject,
    mut v_x_3382_: *mut leanh::LeanObject,
    mut v___y_3383_: *mut leanh::LeanObject,
    mut v___y_3384_: *mut leanh::LeanObject,
    mut v___y_3385_: *mut leanh::LeanObject,
    mut v___y_3386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3397_: u8 = 0;
    let mut v_fst_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3407_: u8 = 0;
    let mut v_a_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3411_: u8 = 0;
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3416_ = lean_array_get_size(v_params_3381_);
                v___x_3417_ = lean_nat_dec_le(v_numParams_3379_, v___x_3380_);
                if v___x_3417_ == 0 {
                    leanh::lean_dec(v___x_3380_);
                    v_lower_3389_ = v_numParams_3379_;
                    v_upper_3390_ = v___x_3416_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_numParams_3379_);
                    v_lower_3389_ = v___x_3380_;
                    v_upper_3390_ = v___x_3416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3391_ =
                    l_Array_toSubarray___redArg(v_params_3381_, v_lower_3389_, v_upper_3390_);
                v___x_3392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___redArg___closed__0;
                v___x_3393_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___redArg(v___x_3391_, v___x_3392_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
                if leanh::lean_obj_tag(v___x_3393_) == 0 {
                    v_a_3394_ = leanh::lean_ctor_get(v___x_3393_, 0);
                    v_isSharedCheck_3407_ = (!leanh::lean_is_exclusive(v___x_3393_)) as u8;
                    if v_isSharedCheck_3407_ == 0 {
                        v___x_3396_ = v___x_3393_;
                        v_isShared_3397_ = v_isSharedCheck_3407_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3394_);
                        leanh::lean_dec(v___x_3393_);
                        v___x_3396_ = leanh::lean_box(0);
                        v_isShared_3397_ = v_isSharedCheck_3407_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3408_ = leanh::lean_ctor_get(v___x_3393_, 0);
                    v_isSharedCheck_3415_ = (!leanh::lean_is_exclusive(v___x_3393_)) as u8;
                    if v_isSharedCheck_3415_ == 0 {
                        v___x_3410_ = v___x_3393_;
                        v_isShared_3411_ = v_isSharedCheck_3415_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3408_);
                        leanh::lean_dec(v___x_3393_);
                        v___x_3410_ = leanh::lean_box(0);
                        v_isShared_3411_ = v_isSharedCheck_3415_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3398_ = leanh::lean_ctor_get(v_a_3394_, 0);
                leanh::lean_inc(v_fst_3398_);
                leanh::lean_dec(v_a_3394_);
                if leanh::lean_obj_tag(v_fst_3398_) == 0 {
                    v___x_3399_ = leanh::lean_box((v___x_3378_) as usize);
                    if v_isShared_3397_ == 0 {
                        leanh::lean_ctor_set(v___x_3396_, 0, v___x_3399_);
                        v___x_3401_ = v___x_3396_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3402_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
                        v___x_3401_ = v_reuseFailAlloc_3402_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_3403_ = leanh::lean_ctor_get(v_fst_3398_, 0);
                    leanh::lean_inc(v_val_3403_);
                    leanh::lean_dec_ref_known(v_fst_3398_, 1);
                    if v_isShared_3397_ == 0 {
                        leanh::lean_ctor_set(v___x_3396_, 0, v_val_3403_);
                        v___x_3405_ = v___x_3396_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3406_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_val_3403_);
                        v___x_3405_ = v_reuseFailAlloc_3406_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3401_;
            }
            4 => {
                return v___x_3405_;
            }
            5 => {
                if v_isShared_3411_ == 0 {
                    v___x_3413_ = v___x_3410_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3414_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
                    v___x_3413_ = v_reuseFailAlloc_3414_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___lam__0___boxed(
    mut v___x_3418_: *mut leanh::LeanObject,
    mut v_numParams_3419_: *mut leanh::LeanObject,
    mut v___x_3420_: *mut leanh::LeanObject,
    mut v_params_3421_: *mut leanh::LeanObject,
    mut v_x_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
    mut v___y_3427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8256__boxed_3428_: u8 = 0;
    let mut v_res_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8256__boxed_3428_ = (leanh::lean_unbox(v___x_3418_) as u8);
    v_res_3429_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___lam__0(v___x_8256__boxed_3428_, v_numParams_3419_, v___x_3420_, v_params_3421_, v_x_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
    leanh::lean_dec(v___y_3426_);
    leanh::lean_dec_ref(v___y_3425_);
    leanh::lean_dec(v___y_3424_);
    leanh::lean_dec_ref(v___y_3423_);
    leanh::lean_dec_ref(v_x_3422_);
    return v_res_3429_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3433_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__2;
    v___x_3434_ = leanh::lean_unsigned_to_nat(62);
    v___x_3435_ = leanh::lean_unsigned_to_nat(75);
    v___x_3436_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__1;
    v___x_3437_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__0;
    v___x_3438_ = l_mkPanicMessageWithDecl(
        v___x_3437_,
        v___x_3436_,
        v___x_3435_,
        v___x_3434_,
        v___x_3433_,
    );
    return v___x_3438_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__5()
-> u64 {
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: u64 = 0;
    v___x_3445_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__4;
    v___x_3446_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3447_: u64 = 0;
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3447_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__5_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__5);
    v___x_3448_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__4;
    v___x_3449_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_3449_, 0, v___x_3448_);
    leanh::lean_ctor_set_uint64(
        v___x_3449_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3447_,
    );
    return v___x_3449_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3450_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3450_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3451_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__7), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__7_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__7);
    v___x_3452_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3452_, 0, v___x_3451_);
    return v___x_3452_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3453_ = leanh::lean_unsigned_to_nat(32);
    v___x_3454_ = lean_mk_empty_array_with_capacity(v___x_3453_);
    v___x_3455_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3455_, 0, v___x_3454_);
    return v___x_3455_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3456_: usize = 0;
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3456_ = 5usize;
    v___x_3457_ = leanh::lean_unsigned_to_nat(0);
    v___x_3458_ = leanh::lean_unsigned_to_nat(32);
    v___x_3459_ = lean_mk_empty_array_with_capacity(v___x_3458_);
    v___x_3460_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__9), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__9_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__9);
    v___x_3461_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3461_, 0, v___x_3460_);
    leanh::lean_ctor_set(v___x_3461_, 1, v___x_3459_);
    leanh::lean_ctor_set(v___x_3461_, 2, v___x_3457_);
    leanh::lean_ctor_set(v___x_3461_, 3, v___x_3457_);
    leanh::lean_ctor_set_usize(v___x_3461_, 4, v___x_3456_);
    return v___x_3461_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3462_ = leanh::lean_box(1);
    v___x_3463_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__10), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__10_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__10);
    v___x_3464_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8);
    v___x_3465_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3465_, 0, v___x_3464_);
    leanh::lean_ctor_set(v___x_3465_, 1, v___x_3463_);
    leanh::lean_ctor_set(v___x_3465_, 2, v___x_3462_);
    return v___x_3465_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3468_: u8 = 0;
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: u8 = 0;
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3468_ = 1;
    v___x_3469_ = leanh::lean_unsigned_to_nat(0);
    v___x_3470_ = leanh::lean_box(0);
    v___x_3471_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__12;
    v___x_3472_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__11), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__11_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__11);
    v___x_3473_ = leanh::lean_box(1);
    v___x_3474_ = 0;
    v___x_3475_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__6), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__6_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__6);
    v___x_3476_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
    leanh::lean_ctor_set(v___x_3476_, 0, v___x_3475_);
    leanh::lean_ctor_set(v___x_3476_, 1, v___x_3473_);
    leanh::lean_ctor_set(v___x_3476_, 2, v___x_3472_);
    leanh::lean_ctor_set(v___x_3476_, 3, v___x_3471_);
    leanh::lean_ctor_set(v___x_3476_, 4, v___x_3470_);
    leanh::lean_ctor_set(v___x_3476_, 5, v___x_3469_);
    leanh::lean_ctor_set(v___x_3476_, 6, v___x_3470_);
    leanh::lean_ctor_set_uint8(
        v___x_3476_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v___x_3474_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3476_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
        v___x_3474_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3476_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
        v___x_3474_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3476_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
        v___x_3468_,
    );
    return v___x_3476_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3477_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8);
    v___x_3478_ = leanh::lean_unsigned_to_nat(0);
    v___x_3479_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3479_, 0, v___x_3478_);
    leanh::lean_ctor_set(v___x_3479_, 1, v___x_3478_);
    leanh::lean_ctor_set(v___x_3479_, 2, v___x_3478_);
    leanh::lean_ctor_set(v___x_3479_, 3, v___x_3478_);
    leanh::lean_ctor_set(v___x_3479_, 4, v___x_3477_);
    leanh::lean_ctor_set(v___x_3479_, 5, v___x_3477_);
    leanh::lean_ctor_set(v___x_3479_, 6, v___x_3477_);
    leanh::lean_ctor_set(v___x_3479_, 7, v___x_3477_);
    leanh::lean_ctor_set(v___x_3479_, 8, v___x_3477_);
    leanh::lean_ctor_set(v___x_3479_, 9, v___x_3477_);
    return v___x_3479_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3480_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8);
    v___x_3481_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_3481_, 0, v___x_3480_);
    leanh::lean_ctor_set(v___x_3481_, 1, v___x_3480_);
    leanh::lean_ctor_set(v___x_3481_, 2, v___x_3480_);
    leanh::lean_ctor_set(v___x_3481_, 3, v___x_3480_);
    leanh::lean_ctor_set(v___x_3481_, 4, v___x_3480_);
    leanh::lean_ctor_set(v___x_3481_, 5, v___x_3480_);
    return v___x_3481_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3482_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__8);
    v___x_3483_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3483_, 0, v___x_3482_);
    leanh::lean_ctor_set(v___x_3483_, 1, v___x_3482_);
    leanh::lean_ctor_set(v___x_3483_, 2, v___x_3482_);
    leanh::lean_ctor_set(v___x_3483_, 3, v___x_3482_);
    leanh::lean_ctor_set(v___x_3483_, 4, v___x_3482_);
    return v___x_3483_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3484_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__16), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__16_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__16);
    v___x_3485_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__10), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__10_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__10);
    v___x_3486_ = leanh::lean_box(1);
    v___x_3487_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__15), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__15_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__15);
    v___x_3488_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__14), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__14_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__14);
    v___x_3489_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3489_, 0, v___x_3488_);
    leanh::lean_ctor_set(v___x_3489_, 1, v___x_3487_);
    leanh::lean_ctor_set(v___x_3489_, 2, v___x_3486_);
    leanh::lean_ctor_set(v___x_3489_, 3, v___x_3485_);
    leanh::lean_ctor_set(v___x_3489_, 4, v___x_3484_);
    return v___x_3489_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg(
    mut v___x_3490_: *mut leanh::LeanObject,
    mut v_as_x27_3491_: *mut leanh::LeanObject,
    mut v_b_3492_: *mut leanh::LeanObject,
    mut v___y_3493_: *mut leanh::LeanObject,
    mut v___y_3494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3500_: u8 = 0;
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3514_: u8 = 0;
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3518_: u8 = 0;
    let mut v___x_3519_: u8 = 0;
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: u8 = 0;
    let mut v_a_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v_a_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3491_) == 0 {
                    leanh::lean_dec_ref(v___x_3490_);
                    v___x_3496_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3496_, 0, v_b_3492_);
                    return v___x_3496_;
                } else {
                    v_head_3497_ = leanh::lean_ctor_get(v_as_x27_3491_, 0);
                    v_tail_3498_ = leanh::lean_ctor_get(v_as_x27_3491_, 1);
                    v___x_3519_ = 0;
                    leanh::lean_inc(v_head_3497_);
                    leanh::lean_inc_ref(v___x_3490_);
                    v___x_3520_ =
                        l_Lean_Environment_find_x3f(v___x_3490_, v_head_3497_, v___x_3519_);
                    if leanh::lean_obj_tag(v___x_3520_) == 1 {
                        v_val_3521_ = leanh::lean_ctor_get(v___x_3520_, 0);
                        leanh::lean_inc(v_val_3521_);
                        leanh::lean_dec_ref_known(v___x_3520_, 1);
                        if leanh::lean_obj_tag(v_val_3521_) == 6 {
                            v_val_3522_ = leanh::lean_ctor_get(v_val_3521_, 0);
                            leanh::lean_inc_ref(v_val_3522_);
                            leanh::lean_dec_ref_known(v_val_3521_, 1);
                            v___x_3523_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3524_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__13), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__13_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__13);
                            v___x_3525_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__17), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__17_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__17);
                            v___x_3526_ = lean_st_mk_ref(v___x_3525_);
                            v_toConstantVal_3527_ = leanh::lean_ctor_get(v_val_3522_, 0);
                            leanh::lean_inc_ref(v_toConstantVal_3527_);
                            v_numParams_3528_ = leanh::lean_ctor_get(v_val_3522_, 3);
                            leanh::lean_inc(v_numParams_3528_);
                            leanh::lean_dec_ref(v_val_3522_);
                            v_type_3529_ = leanh::lean_ctor_get(v_toConstantVal_3527_, 2);
                            leanh::lean_inc_ref(v_type_3529_);
                            leanh::lean_dec_ref(v_toConstantVal_3527_);
                            v___x_3530_ = leanh::lean_box((v___x_3519_) as usize);
                            v___f_3531_ = leanh::lean_alloc_closure(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                            leanh::lean_closure_set(v___f_3531_, 0, v___x_3530_);
                            leanh::lean_closure_set(v___f_3531_, 1, v_numParams_3528_);
                            leanh::lean_closure_set(v___f_3531_, 2, v___x_3523_);
                            v___x_3532_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___redArg(v_type_3529_, v___f_3531_, v___x_3519_, v___x_3524_, v___x_3526_, v___y_3493_, v___y_3494_);
                            if leanh::lean_obj_tag(v___x_3532_) == 0 {
                                v_a_3533_ = leanh::lean_ctor_get(v___x_3532_, 0);
                                leanh::lean_inc(v_a_3533_);
                                leanh::lean_dec_ref_known(v___x_3532_, 1);
                                v___x_3534_ = lean_st_ref_get(v___x_3526_);
                                leanh::lean_dec(v___x_3526_);
                                leanh::lean_dec(v___x_3534_);
                                v___x_3535_ = (leanh::lean_unbox(v_a_3533_) as u8);
                                leanh::lean_dec(v_a_3533_);
                                v_a_3500_ = v___x_3535_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3526_);
                                if leanh::lean_obj_tag(v___x_3532_) == 0 {
                                    v_a_3536_ = leanh::lean_ctor_get(v___x_3532_, 0);
                                    leanh::lean_inc(v_a_3536_);
                                    leanh::lean_dec_ref_known(v___x_3532_, 1);
                                    v___x_3537_ = (leanh::lean_unbox(v_a_3536_) as u8);
                                    leanh::lean_dec(v_a_3536_);
                                    v_a_3500_ = v___x_3537_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_b_3492_);
                                    leanh::lean_dec_ref(v___x_3490_);
                                    v_a_3538_ = leanh::lean_ctor_get(v___x_3532_, 0);
                                    v_isSharedCheck_3545_ =
                                        (!leanh::lean_is_exclusive(v___x_3532_)) as u8;
                                    if v_isSharedCheck_3545_ == 0 {
                                        v___x_3540_ = v___x_3532_;
                                        v_isShared_3541_ = v_isSharedCheck_3545_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3538_);
                                        leanh::lean_dec(v___x_3532_);
                                        v___x_3540_ = leanh::lean_box(0);
                                        v_isShared_3541_ = v_isSharedCheck_3545_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_val_3521_);
                            v___y_3506_ = v___y_3493_;
                            v___y_3507_ = v___y_3494_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3520_);
                        v___y_3506_ = v___y_3493_;
                        v___y_3507_ = v___y_3494_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                if v_a_3500_ == 0 {
                    v___x_3501_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3502_ = lean_nat_add(v_b_3492_, v___x_3501_);
                    leanh::lean_dec(v_b_3492_);
                    v_as_x27_3491_ = v_tail_3498_;
                    v_b_3492_ = v___x_3502_;
                    state = 0;
                    continue;
                } else {
                    v_as_x27_3491_ = v_tail_3498_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_3508_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__3_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__3);
                v___x_3509_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__0(v___x_3508_, v___y_3506_, v___y_3507_);
                if leanh::lean_obj_tag(v___x_3509_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3509_, 1);
                    v_as_x27_3491_ = v_tail_3498_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_b_3492_);
                    leanh::lean_dec_ref(v___x_3490_);
                    v_a_3511_ = leanh::lean_ctor_get(v___x_3509_, 0);
                    v_isSharedCheck_3518_ = (!leanh::lean_is_exclusive(v___x_3509_)) as u8;
                    if v_isSharedCheck_3518_ == 0 {
                        v___x_3513_ = v___x_3509_;
                        v_isShared_3514_ = v_isSharedCheck_3518_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3511_);
                        leanh::lean_dec(v___x_3509_);
                        v___x_3513_ = leanh::lean_box(0);
                        v_isShared_3514_ = v_isSharedCheck_3518_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3514_ == 0 {
                    v___x_3516_ = v___x_3513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3517_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
                    v___x_3516_ = v_reuseFailAlloc_3517_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3516_;
            }
            5 => {
                if v_isShared_3541_ == 0 {
                    v___x_3543_ = v___x_3540_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3544_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
                    v___x_3543_ = v_reuseFailAlloc_3544_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___boxed(
    mut v___x_3546_: *mut leanh::LeanObject,
    mut v_as_x27_3547_: *mut leanh::LeanObject,
    mut v_b_3548_: *mut leanh::LeanObject,
    mut v___y_3549_: *mut leanh::LeanObject,
    mut v___y_3550_: *mut leanh::LeanObject,
    mut v___y_3551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3552_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg(v___x_3546_, v_as_x27_3547_, v_b_3548_, v___y_3549_, v___y_3550_);
    leanh::lean_dec(v___y_3550_);
    leanh::lean_dec_ref(v___y_3549_);
    leanh::lean_dec(v_as_x27_3547_);
    return v_res_3552_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3556_ = leanh::lean_box(0);
    v___x_3557_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__1;
    v___x_3558_ = l_Lean_Expr_const___override(v___x_3557_, v___x_3556_);
    return v___x_3558_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3562_ = leanh::lean_box(0);
    v___x_3563_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__4;
    v___x_3564_ = l_Lean_Expr_const___override(v___x_3563_, v___x_3562_);
    return v___x_3564_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3574_ = leanh::lean_box(0);
    v___x_3575_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__13;
    v___x_3576_ = l_Lean_Expr_const___override(v___x_3575_, v___x_3574_);
    return v___x_3576_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3579_ = leanh::lean_box(0);
    v___x_3580_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__15;
    v___x_3581_ = l_Lean_Expr_const___override(v___x_3580_, v___x_3579_);
    return v___x_3581_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3584_ = leanh::lean_box(0);
    v___x_3585_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__17;
    v___x_3586_ = l_Lean_Expr_const___override(v___x_3585_, v___x_3584_);
    return v___x_3586_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3589_ = leanh::lean_box(0);
    v___x_3590_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__19;
    v___x_3591_ = l_Lean_Expr_const___override(v___x_3590_, v___x_3589_);
    return v___x_3591_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3594_ = leanh::lean_box(0);
    v___x_3595_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__21;
    v___x_3596_ = l_Lean_Expr_const___override(v___x_3595_, v___x_3594_);
    return v___x_3596_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3599_ = leanh::lean_box(0);
    v___x_3600_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__23;
    v___x_3601_ = l_Lean_Expr_const___override(v___x_3600_, v___x_3599_);
    return v___x_3601_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache(
    mut v_name_3602_: *mut leanh::LeanObject,
    mut v_a_3603_: *mut leanh::LeanObject,
    mut v_a_3604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: u8 = 0;
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: u8 = 0;
    let mut v___x_3627_: u8 = 0;
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut v_a_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v_pre_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: u8 = 0;
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: u8 = 0;
    let mut v___x_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: u8 = 0;
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: u8 = 0;
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: u8 = 0;
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: u8 = 0;
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: u8 = 0;
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: u8 = 0;
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_name_3602_) == 1 {
                    v_pre_3649_ = leanh::lean_ctor_get(v_name_3602_, 0);
                    if leanh::lean_obj_tag(v_pre_3649_) == 0 {
                        v_str_3650_ = leanh::lean_ctor_get(v_name_3602_, 1);
                        v___x_3651_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9;
                        v___x_3652_ = lean_string_dec_eq(v_str_3650_, v___x_3651_);
                        if v___x_3652_ == 0 {
                            v___x_3653_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6;
                            v___x_3654_ = lean_string_dec_eq(v_str_3650_, v___x_3653_);
                            if v___x_3654_ == 0 {
                                v___x_3655_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3;
                                v___x_3656_ = lean_string_dec_eq(v_str_3650_, v___x_3655_);
                                if v___x_3656_ == 0 {
                                    v___x_3657_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__6;
                                    v___x_3658_ = lean_string_dec_eq(v_str_3650_, v___x_3657_);
                                    if v___x_3658_ == 0 {
                                        v___x_3659_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__7;
                                        v___x_3660_ = lean_string_dec_eq(v_str_3650_, v___x_3659_);
                                        if v___x_3660_ == 0 {
                                            v___x_3661_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__8;
                                            v___x_3662_ =
                                                lean_string_dec_eq(v_str_3650_, v___x_3661_);
                                            if v___x_3662_ == 0 {
                                                v___x_3663_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__9;
                                                v___x_3664_ =
                                                    lean_string_dec_eq(v_str_3650_, v___x_3663_);
                                                if v___x_3664_ == 0 {
                                                    v___x_3665_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__10;
                                                    v___x_3666_ = lean_string_dec_eq(
                                                        v_str_3650_,
                                                        v___x_3665_,
                                                    );
                                                    if v___x_3666_ == 0 {
                                                        v___x_3667_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__11;
                                                        v___x_3668_ = lean_string_dec_eq(
                                                            v_str_3650_,
                                                            v___x_3667_,
                                                        );
                                                        if v___x_3668_ == 0 {
                                                            v___x_3669_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__12;
                                                            v___x_3670_ = lean_string_dec_eq(
                                                                v_str_3650_,
                                                                v___x_3669_,
                                                            );
                                                            if v___x_3670_ == 0 {
                                                                v___y_3610_ = v_a_3603_;
                                                                v___y_3611_ = v_a_3604_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                leanh::lean_dec_ref_known(
                                                                    v_name_3602_,
                                                                    2,
                                                                );
                                                                v___x_3671_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__14_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__14);
                                                                v___x_3672_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_3672_,
                                                                    0,
                                                                    v___x_3671_,
                                                                );
                                                                return v___x_3672_;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref_known(
                                                                v_name_3602_,
                                                                2,
                                                            );
                                                            v___x_3673_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2);
                                                            v___x_3674_ =
                                                                leanh::lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_3674_,
                                                                0,
                                                                v___x_3673_,
                                                            );
                                                            return v___x_3674_;
                                                        }
                                                    } else {
                                                        leanh::lean_dec_ref_known(
                                                            v_name_3602_,
                                                            2,
                                                        );
                                                        v___x_3675_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__16), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__16_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__16);
                                                        v___x_3676_ = leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        leanh::lean_ctor_set(
                                                            v___x_3676_,
                                                            0,
                                                            v___x_3675_,
                                                        );
                                                        return v___x_3676_;
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref_known(
                                                        v_name_3602_,
                                                        2,
                                                    );
                                                    v___x_3677_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__18_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__18);
                                                    v___x_3678_ = leanh::lean_alloc_ctor(
                                                        0,
                                                        1,
                                                        (0) as u32,
                                                    );
                                                    leanh::lean_ctor_set(
                                                        v___x_3678_,
                                                        0,
                                                        v___x_3677_,
                                                    );
                                                    return v___x_3678_;
                                                }
                                            } else {
                                                leanh::lean_dec_ref_known(v_name_3602_, 2);
                                                v___x_3679_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__20), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__20_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__20);
                                                v___x_3680_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3680_,
                                                    0,
                                                    v___x_3679_,
                                                );
                                                return v___x_3680_;
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_name_3602_, 2);
                                            v___x_3681_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__22_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__22);
                                            v___x_3682_ =
                                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v___x_3682_,
                                                0,
                                                v___x_3681_,
                                            );
                                            return v___x_3682_;
                                        }
                                    } else {
                                        leanh::lean_dec_ref_known(v_name_3602_, 2);
                                        v___x_3683_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__24_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__24);
                                        v___x_3684_ =
                                            leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3684_, 0, v___x_3683_);
                                        return v___x_3684_;
                                    }
                                } else {
                                    leanh::lean_dec_ref_known(v_name_3602_, 2);
                                    v___x_3685_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__5);
                                    v___x_3686_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3686_, 0, v___x_3685_);
                                    return v___x_3686_;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_name_3602_, 2);
                                v___x_3687_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__8);
                                v___x_3688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3688_, 0, v___x_3687_);
                                return v___x_3688_;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_name_3602_, 2);
                            v___x_3689_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__11);
                            v___x_3690_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3690_, 0, v___x_3689_);
                            return v___x_3690_;
                        }
                    } else {
                        v___y_3610_ = v_a_3603_;
                        v___y_3611_ = v_a_3604_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___y_3610_ = v_a_3603_;
                    v___y_3611_ = v_a_3604_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3607_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2);
                v___x_3608_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3608_, 0, v___x_3607_);
                return v___x_3608_;
            }
            2 => {
                v___x_3612_ = lean_st_ref_get(v___y_3611_);
                v_env_3613_ = leanh::lean_ctor_get(v___x_3612_, 0);
                leanh::lean_inc_ref_n(v_env_3613_, 2);
                leanh::lean_dec(v___x_3612_);
                v___x_3614_ = 0;
                v___x_3615_ = l_Lean_Environment_find_x3f(v_env_3613_, v_name_3602_, v___x_3614_);
                if leanh::lean_obj_tag(v___x_3615_) == 1 {
                    v_val_3616_ = leanh::lean_ctor_get(v___x_3615_, 0);
                    leanh::lean_inc(v_val_3616_);
                    leanh::lean_dec_ref_known(v___x_3615_, 1);
                    if leanh::lean_obj_tag(v_val_3616_) == 5 {
                        v_val_3617_ = leanh::lean_ctor_get(v_val_3616_, 0);
                        leanh::lean_inc_ref(v_val_3617_);
                        leanh::lean_dec_ref_known(v_val_3616_, 1);
                        v_ctors_3618_ = leanh::lean_ctor_get(v_val_3617_, 4);
                        leanh::lean_inc(v_ctors_3618_);
                        leanh::lean_dec_ref(v_val_3617_);
                        v___x_3619_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3620_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg(v_env_3613_, v_ctors_3618_, v___x_3619_, v___y_3610_, v___y_3611_);
                        if leanh::lean_obj_tag(v___x_3620_) == 0 {
                            v_a_3621_ = leanh::lean_ctor_get(v___x_3620_, 0);
                            v_isSharedCheck_3640_ =
                                (!leanh::lean_is_exclusive(v___x_3620_)) as u8;
                            if v_isSharedCheck_3640_ == 0 {
                                v___x_3623_ = v___x_3620_;
                                v_isShared_3624_ = v_isSharedCheck_3640_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3621_);
                                leanh::lean_dec(v___x_3620_);
                                v___x_3623_ = leanh::lean_box(0);
                                v_isShared_3624_ = v_isSharedCheck_3640_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_ctors_3618_);
                            v_a_3641_ = leanh::lean_ctor_get(v___x_3620_, 0);
                            v_isSharedCheck_3648_ =
                                (!leanh::lean_is_exclusive(v___x_3620_)) as u8;
                            if v_isSharedCheck_3648_ == 0 {
                                v___x_3643_ = v___x_3620_;
                                v_isShared_3644_ = v_isSharedCheck_3648_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3641_);
                                leanh::lean_dec(v___x_3620_);
                                v___x_3643_ = leanh::lean_box(0);
                                v_isShared_3644_ = v_isSharedCheck_3648_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_3616_);
                        leanh::lean_dec_ref(v_env_3613_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3615_);
                    leanh::lean_dec_ref(v_env_3613_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3625_ = l_List_lengthTR___redArg(v_ctors_3618_);
                leanh::lean_dec(v_ctors_3618_);
                v___x_3626_ = lean_nat_dec_eq(v_a_3621_, v___x_3625_);
                if v___x_3626_ == 0 {
                    leanh::lean_dec(v___x_3625_);
                    v___x_3627_ = lean_nat_dec_eq(v_a_3621_, v___x_3619_);
                    leanh::lean_dec(v_a_3621_);
                    if v___x_3627_ == 0 {
                        v___x_3628_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2);
                        if v_isShared_3624_ == 0 {
                            leanh::lean_ctor_set(v___x_3623_, 0, v___x_3628_);
                            v___x_3630_ = v___x_3623_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3631_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
                            v___x_3630_ = v_reuseFailAlloc_3631_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_3632_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__5_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__5);
                        if v_isShared_3624_ == 0 {
                            leanh::lean_ctor_set(v___x_3623_, 0, v___x_3632_);
                            v___x_3634_ = v___x_3623_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3635_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
                            v___x_3634_ = v_reuseFailAlloc_3635_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3621_);
                    v___x_3636_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum(v___x_3625_);
                    leanh::lean_dec(v___x_3625_);
                    if v_isShared_3624_ == 0 {
                        leanh::lean_ctor_set(v___x_3623_, 0, v___x_3636_);
                        v___x_3638_ = v___x_3623_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3639_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
                        v___x_3638_ = v_reuseFailAlloc_3639_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3630_;
            }
            5 => {
                return v___x_3634_;
            }
            6 => {
                return v___x_3638_;
            }
            7 => {
                if v_isShared_3644_ == 0 {
                    v___x_3646_ = v___x_3643_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3647_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
                    v___x_3646_ = v_reuseFailAlloc_3647_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___boxed(
    mut v_name_3691_: *mut leanh::LeanObject,
    mut v_a_3692_: *mut leanh::LeanObject,
    mut v_a_3693_: *mut leanh::LeanObject,
    mut v_a_3694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3695_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache(v_name_3691_, v_a_3692_, v_a_3693_);
    leanh::lean_dec(v_a_3693_);
    leanh::lean_dec_ref(v_a_3692_);
    return v_res_3695_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1(
    mut v_inst_3696_: *mut leanh::LeanObject,
    mut v_R_3697_: *mut leanh::LeanObject,
    mut v_a_3698_: *mut leanh::LeanObject,
    mut v_b_3699_: *mut leanh::LeanObject,
    mut v_c_3700_: *mut leanh::LeanObject,
    mut v___y_3701_: *mut leanh::LeanObject,
    mut v___y_3702_: *mut leanh::LeanObject,
    mut v___y_3703_: *mut leanh::LeanObject,
    mut v___y_3704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___redArg(v_a_3698_, v_b_3699_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
    return v___x_3706_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1___boxed(
    mut v_inst_3707_: *mut leanh::LeanObject,
    mut v_R_3708_: *mut leanh::LeanObject,
    mut v_a_3709_: *mut leanh::LeanObject,
    mut v_b_3710_: *mut leanh::LeanObject,
    mut v_c_3711_: *mut leanh::LeanObject,
    mut v___y_3712_: *mut leanh::LeanObject,
    mut v___y_3713_: *mut leanh::LeanObject,
    mut v___y_3714_: *mut leanh::LeanObject,
    mut v___y_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__1(v_inst_3707_, v_R_3708_, v_a_3709_, v_b_3710_, v_c_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
    leanh::lean_dec(v___y_3715_);
    leanh::lean_dec_ref(v___y_3714_);
    leanh::lean_dec(v___y_3713_);
    leanh::lean_dec_ref(v___y_3712_);
    return v_res_3717_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3(
    mut v___x_3718_: *mut leanh::LeanObject,
    mut v_as_3719_: *mut leanh::LeanObject,
    mut v_as_x27_3720_: *mut leanh::LeanObject,
    mut v_b_3721_: *mut leanh::LeanObject,
    mut v_a_3722_: *mut leanh::LeanObject,
    mut v___y_3723_: *mut leanh::LeanObject,
    mut v___y_3724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3726_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg(v___x_3718_, v_as_x27_3720_, v_b_3721_, v___y_3723_, v___y_3724_);
    return v___x_3726_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___boxed(
    mut v___x_3727_: *mut leanh::LeanObject,
    mut v_as_3728_: *mut leanh::LeanObject,
    mut v_as_x27_3729_: *mut leanh::LeanObject,
    mut v_b_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
    mut v___y_3732_: *mut leanh::LeanObject,
    mut v___y_3733_: *mut leanh::LeanObject,
    mut v___y_3734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3735_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3(v___x_3727_, v_as_3728_, v_as_x27_3729_, v_b_3730_, v_a_3731_, v___y_3732_, v___y_3733_);
    leanh::lean_dec(v___y_3733_);
    leanh::lean_dec_ref(v___y_3732_);
    leanh::lean_dec(v_as_x27_3729_);
    leanh::lean_dec(v_as_3728_);
    return v_res_3735_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3738_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__1;
    v___x_3739_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__0;
    v___x_3740_ = l_Lean_PersistentHashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3739_,
        v___x_3738_,
    );
    return v___x_3740_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3741_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__2);
    v___x_3742_ = leanh::lean_box(0);
    v___x_3743_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3743_, 0, v___x_3742_);
    leanh::lean_ctor_set(v___x_3743_, 1, v___x_3741_);
    return v___x_3743_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(
    mut v_ext_3744_: *mut leanh::LeanObject,
    mut v_a_3745_: *mut leanh::LeanObject,
    mut v_a_3746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3748_ = lean_st_ref_get(v_a_3746_);
    v_env_3749_ = leanh::lean_ctor_get(v___x_3748_, 0);
    leanh::lean_inc_ref(v_env_3749_);
    leanh::lean_dec(v___x_3748_);
    v_asyncMode_3750_ = leanh::lean_ctor_get(v_ext_3744_, 2);
    v___x_3751_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__3);
    v___x_3752_ = leanh::lean_box(0);
    v___x_3753_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_3751_,
        v_ext_3744_,
        v_env_3749_,
        v_asyncMode_3750_,
        v___x_3752_,
    );
    v_snd_3754_ = leanh::lean_ctor_get(v___x_3753_, 1);
    leanh::lean_inc(v_snd_3754_);
    leanh::lean_dec(v___x_3753_);
    v___x_3755_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_3754_, v_a_3745_);
    leanh::lean_dec(v_snd_3754_);
    v___x_3756_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3756_, 0, v___x_3755_);
    return v___x_3756_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___boxed(
    mut v_ext_3757_: *mut leanh::LeanObject,
    mut v_a_3758_: *mut leanh::LeanObject,
    mut v_a_3759_: *mut leanh::LeanObject,
    mut v_a_3760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3761_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_ext_3757_, v_a_3758_, v_a_3759_);
    leanh::lean_dec(v_a_3759_);
    leanh::lean_dec(v_a_3758_);
    leanh::lean_dec_ref(v_ext_3757_);
    return v_res_3761_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___lam__0(
    mut v_a_3762_: *mut leanh::LeanObject,
    mut v_b_3763_: *mut leanh::LeanObject,
    mut v_x_3764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3769_: u8 = 0;
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3765_ = leanh::lean_ctor_get(v_x_3764_, 0);
                v_snd_3766_ = leanh::lean_ctor_get(v_x_3764_, 1);
                v_isSharedCheck_3775_ = (!leanh::lean_is_exclusive(v_x_3764_)) as u8;
                if v_isSharedCheck_3775_ == 0 {
                    v___x_3768_ = v_x_3764_;
                    v_isShared_3769_ = v_isSharedCheck_3775_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3766_);
                    leanh::lean_inc(v_fst_3765_);
                    leanh::lean_dec(v_x_3764_);
                    v___x_3768_ = leanh::lean_box(0);
                    v_isShared_3769_ = v_isSharedCheck_3775_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_3762_);
                v___x_3770_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3770_, 0, v_a_3762_);
                leanh::lean_ctor_set(v___x_3770_, 1, v_fst_3765_);
                v___x_3771_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_3766_, v_a_3762_, v_b_3763_);
                if v_isShared_3769_ == 0 {
                    leanh::lean_ctor_set(v___x_3768_, 1, v___x_3771_);
                    leanh::lean_ctor_set(v___x_3768_, 0, v___x_3770_);
                    v___x_3773_ = v___x_3768_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 1, v___x_3771_);
                    v___x_3773_ = v_reuseFailAlloc_3774_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3776_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3777_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__0_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__0);
    v___x_3778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3778_, 0, v___x_3777_);
    return v___x_3778_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3779_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__1);
    v___x_3780_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3780_, 0, v___x_3779_);
    leanh::lean_ctor_set(v___x_3780_, 1, v___x_3779_);
    return v___x_3780_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg(
    mut v_ext_3781_: *mut leanh::LeanObject,
    mut v_a_3782_: *mut leanh::LeanObject,
    mut v_b_3783_: *mut leanh::LeanObject,
    mut v_a_3784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v_asyncMode_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3809_: u8 = 0;
    let mut v_unused_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3786_ = lean_st_ref_take(v_a_3784_);
                v_env_3787_ = leanh::lean_ctor_get(v___x_3786_, 0);
                v_nextMacroScope_3788_ = leanh::lean_ctor_get(v___x_3786_, 1);
                v_ngen_3789_ = leanh::lean_ctor_get(v___x_3786_, 2);
                v_auxDeclNGen_3790_ = leanh::lean_ctor_get(v___x_3786_, 3);
                v_traceState_3791_ = leanh::lean_ctor_get(v___x_3786_, 4);
                v_messages_3792_ = leanh::lean_ctor_get(v___x_3786_, 6);
                v_infoState_3793_ = leanh::lean_ctor_get(v___x_3786_, 7);
                v_snapshotTasks_3794_ = leanh::lean_ctor_get(v___x_3786_, 8);
                v_isSharedCheck_3809_ = (!leanh::lean_is_exclusive(v___x_3786_)) as u8;
                if v_isSharedCheck_3809_ == 0 {
                    v_unused_3810_ = leanh::lean_ctor_get(v___x_3786_, 5);
                    leanh::lean_dec(v_unused_3810_);
                    v___x_3796_ = v___x_3786_;
                    v_isShared_3797_ = v_isSharedCheck_3809_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3794_);
                    leanh::lean_inc(v_infoState_3793_);
                    leanh::lean_inc(v_messages_3792_);
                    leanh::lean_inc(v_traceState_3791_);
                    leanh::lean_inc(v_auxDeclNGen_3790_);
                    leanh::lean_inc(v_ngen_3789_);
                    leanh::lean_inc(v_nextMacroScope_3788_);
                    leanh::lean_inc(v_env_3787_);
                    leanh::lean_dec(v___x_3786_);
                    v___x_3796_ = leanh::lean_box(0);
                    v_isShared_3797_ = v_isSharedCheck_3809_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_asyncMode_3798_ = leanh::lean_ctor_get(v_ext_3781_, 2);
                leanh::lean_inc(v_asyncMode_3798_);
                v___f_3799_ = leanh::lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_3799_, 0, v_a_3782_);
                leanh::lean_closure_set(v___f_3799_, 1, v_b_3783_);
                v___x_3800_ = leanh::lean_box(0);
                v___x_3801_ = l_Lean_EnvExtension_modifyState___redArg(
                    v_ext_3781_,
                    v_env_3787_,
                    v___f_3799_,
                    v_asyncMode_3798_,
                    v___x_3800_,
                );
                leanh::lean_dec(v_asyncMode_3798_);
                v___x_3802_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__2);
                if v_isShared_3797_ == 0 {
                    leanh::lean_ctor_set(v___x_3796_, 5, v___x_3802_);
                    leanh::lean_ctor_set(v___x_3796_, 0, v___x_3801_);
                    v___x_3804_ = v___x_3796_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3808_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 1, v_nextMacroScope_3788_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 2, v_ngen_3789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 3, v_auxDeclNGen_3790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 4, v_traceState_3791_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 5, v___x_3802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 6, v_messages_3792_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 7, v_infoState_3793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3808_, 8, v_snapshotTasks_3794_);
                    v___x_3804_ = v_reuseFailAlloc_3808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3805_ = lean_st_ref_set(v_a_3784_, v___x_3804_);
                v___x_3806_ = leanh::lean_box(0);
                v___x_3807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3807_, 0, v___x_3806_);
                return v___x_3807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___boxed(
    mut v_ext_3811_: *mut leanh::LeanObject,
    mut v_a_3812_: *mut leanh::LeanObject,
    mut v_b_3813_: *mut leanh::LeanObject,
    mut v_a_3814_: *mut leanh::LeanObject,
    mut v_a_3815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3816_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg(v_ext_3811_, v_a_3812_, v_b_3813_, v_a_3814_);
    leanh::lean_dec(v_a_3814_);
    return v_res_3816_;
}
pub unsafe fn l_Lean_Compiler_LCNF_nameToImpureType(
    mut v_name_3817_: *mut leanh::LeanObject,
    mut v_a_3818_: *mut leanh::LeanObject,
    mut v_a_3819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3826_: u8 = 0;
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3832_: u8 = 0;
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3836_: u8 = 0;
    let mut v_unused_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3821_ =
                    l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt;
                v___x_3822_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v___x_3821_, v_name_3817_, v_a_3819_);
                v_a_3823_ = leanh::lean_ctor_get(v___x_3822_, 0);
                v_isSharedCheck_3842_ = (!leanh::lean_is_exclusive(v___x_3822_)) as u8;
                if v_isSharedCheck_3842_ == 0 {
                    v___x_3825_ = v___x_3822_;
                    v_isShared_3826_ = v_isSharedCheck_3842_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3823_);
                    leanh::lean_dec(v___x_3822_);
                    v___x_3825_ = leanh::lean_box(0);
                    v_isShared_3826_ = v_isSharedCheck_3842_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3823_) == 0 {
                    leanh::lean_del_object(v___x_3825_);
                    leanh::lean_inc(v_name_3817_);
                    v___x_3827_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache(v_name_3817_, v_a_3818_, v_a_3819_);
                    if leanh::lean_obj_tag(v___x_3827_) == 0 {
                        v_a_3828_ = leanh::lean_ctor_get(v___x_3827_, 0);
                        leanh::lean_inc_n(v_a_3828_, 2);
                        leanh::lean_dec_ref_known(v___x_3827_, 1);
                        v___x_3829_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg(v___x_3821_, v_name_3817_, v_a_3828_, v_a_3819_);
                        v_isSharedCheck_3836_ =
                            (!leanh::lean_is_exclusive(v___x_3829_)) as u8;
                        if v_isSharedCheck_3836_ == 0 {
                            v_unused_3837_ = leanh::lean_ctor_get(v___x_3829_, 0);
                            leanh::lean_dec(v_unused_3837_);
                            v___x_3831_ = v___x_3829_;
                            v_isShared_3832_ = v_isSharedCheck_3836_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3829_);
                            v___x_3831_ = leanh::lean_box(0);
                            v_isShared_3832_ = v_isSharedCheck_3836_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_name_3817_);
                        return v___x_3827_;
                    }
                } else {
                    leanh::lean_dec(v_name_3817_);
                    v_val_3838_ = leanh::lean_ctor_get(v_a_3823_, 0);
                    leanh::lean_inc(v_val_3838_);
                    leanh::lean_dec_ref_known(v_a_3823_, 1);
                    if v_isShared_3826_ == 0 {
                        leanh::lean_ctor_set(v___x_3825_, 0, v_val_3838_);
                        v___x_3840_ = v___x_3825_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3841_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_val_3838_);
                        v___x_3840_ = v_reuseFailAlloc_3841_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3832_ == 0 {
                    leanh::lean_ctor_set(v___x_3831_, 0, v_a_3828_);
                    v___x_3834_ = v___x_3831_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3835_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3828_);
                    v___x_3834_ = v_reuseFailAlloc_3835_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3834_;
            }
            4 => {
                return v___x_3840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_nameToImpureType___boxed(
    mut v_name_3843_: *mut leanh::LeanObject,
    mut v_a_3844_: *mut leanh::LeanObject,
    mut v_a_3845_: *mut leanh::LeanObject,
    mut v_a_3846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3847_ = l_Lean_Compiler_LCNF_nameToImpureType(v_name_3843_, v_a_3844_, v_a_3845_);
    leanh::lean_dec(v_a_3845_);
    leanh::lean_dec_ref(v_a_3844_);
    return v_res_3847_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(
    mut v_ext_3848_: *mut leanh::LeanObject,
    mut v_a_3849_: *mut leanh::LeanObject,
    mut v_a_3850_: *mut leanh::LeanObject,
    mut v_a_3851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg(v_ext_3848_, v_a_3849_, v_a_3851_);
    return v___x_3853_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___boxed(
    mut v_ext_3854_: *mut leanh::LeanObject,
    mut v_a_3855_: *mut leanh::LeanObject,
    mut v_a_3856_: *mut leanh::LeanObject,
    mut v_a_3857_: *mut leanh::LeanObject,
    mut v_a_3858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0(v_ext_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
    leanh::lean_dec(v_a_3857_);
    leanh::lean_dec_ref(v_a_3856_);
    leanh::lean_dec(v_a_3855_);
    leanh::lean_dec_ref(v_ext_3854_);
    return v_res_3859_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1(
    mut v_ext_3860_: *mut leanh::LeanObject,
    mut v_a_3861_: *mut leanh::LeanObject,
    mut v_b_3862_: *mut leanh::LeanObject,
    mut v_a_3863_: *mut leanh::LeanObject,
    mut v_a_3864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3866_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg(v_ext_3860_, v_a_3861_, v_b_3862_, v_a_3864_);
    return v___x_3866_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___boxed(
    mut v_ext_3867_: *mut leanh::LeanObject,
    mut v_a_3868_: *mut leanh::LeanObject,
    mut v_b_3869_: *mut leanh::LeanObject,
    mut v_a_3870_: *mut leanh::LeanObject,
    mut v_a_3871_: *mut leanh::LeanObject,
    mut v_a_3872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3873_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1(v_ext_3867_, v_a_3868_, v_b_3869_, v_a_3870_, v_a_3871_);
    leanh::lean_dec(v_a_3871_);
    leanh::lean_dec_ref(v_a_3870_);
    return v_res_3873_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(
    mut v_type_3875_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_declName_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: u8 = 0;
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3882_: u8 = 0;
    let mut v_body_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_type_3875_) {
                4 => {
                    v_declName_3876_ = leanh::lean_ctor_get(v_type_3875_, 0);
                    if leanh::lean_obj_tag(v_declName_3876_) == 1 {
                        v_pre_3877_ = leanh::lean_ctor_get(v_declName_3876_, 0);
                        if leanh::lean_obj_tag(v_pre_3877_) == 0 {
                            v_str_3878_ = leanh::lean_ctor_get(v_declName_3876_, 1);
                            v___x_3879_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___closed__0;
                            v___x_3880_ = lean_string_dec_eq(v_str_3878_, v___x_3879_);
                            return v___x_3880_;
                        } else {
                            v___x_3881_ = 0;
                            return v___x_3881_;
                        }
                    } else {
                        v___x_3882_ = 0;
                        return v___x_3882_;
                    }
                }
                7 => {
                    v_body_3883_ = leanh::lean_ctor_get(v_type_3875_, 2);
                    v_type_3875_ = v_body_3883_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_3885_ = 0;
                    return v___x_3885_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType___boxed(
    mut v_type_3886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3887_: u8 = 0;
    let mut v_r_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3887_ =
        l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(
            v_type_3886_,
        );
    leanh::lean_dec_ref(v_type_3886_);
    v_r_3888_ = leanh::lean_box((v_res_3887_) as usize);
    return v_r_3888_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(
    mut v_msg_3889_: *mut leanh::LeanObject,
    mut v___y_3890_: *mut leanh::LeanObject,
    mut v___y_3891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938__overap_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3893_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__0___closed__0;
    v___x_938__overap_3894_ = lean_panic_fn_borrowed(v___f_3893_, v_msg_3889_);
    leanh::lean_inc(v___y_3891_);
    leanh::lean_inc_ref(v___y_3890_);
    v___x_3895_ = leanh::lean_apply_3(
        v___x_938__overap_3894_,
        v___y_3890_,
        v___y_3891_,
        leanh::lean_box(0),
    );
    return v___x_3895_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1___boxed(
    mut v_msg_3896_: *mut leanh::LeanObject,
    mut v___y_3897_: *mut leanh::LeanObject,
    mut v___y_3898_: *mut leanh::LeanObject,
    mut v___y_3899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3900_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(
        v_msg_3896_,
        v___y_3897_,
        v___y_3898_,
    );
    leanh::lean_dec(v___y_3898_);
    leanh::lean_dec_ref(v___y_3897_);
    return v_res_3900_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toImpureType___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3903_ = leanh::lean_box(0);
    v_dummy_3904_ = l_Lean_Expr_sort___override(v___x_3903_);
    return v_dummy_3904_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toImpureType___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3906_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__2;
    v___x_3907_ = leanh::lean_unsigned_to_nat(41);
    v___x_3908_ = leanh::lean_unsigned_to_nat(104);
    v___x_3909_ = l_Lean_Compiler_LCNF_toImpureType___closed__2;
    v___x_3910_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__0;
    v___x_3911_ = l_mkPanicMessageWithDecl(
        v___x_3910_,
        v___x_3909_,
        v___x_3908_,
        v___x_3907_,
        v___x_3906_,
    );
    return v___x_3911_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_toImpureType___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3912_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__2;
    v___x_3913_ = leanh::lean_unsigned_to_nat(9);
    v___x_3914_ = leanh::lean_unsigned_to_nat(116);
    v___x_3915_ = l_Lean_Compiler_LCNF_toImpureType___closed__2;
    v___x_3916_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__0;
    v___x_3917_ = l_mkPanicMessageWithDecl(
        v___x_3916_,
        v___x_3915_,
        v___x_3914_,
        v___x_3913_,
        v___x_3912_,
    );
    return v___x_3917_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toImpureType(
    mut v_type_3918_: *mut leanh::LeanObject,
    mut v_a_3919_: *mut leanh::LeanObject,
    mut v_a_3920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: u8 = 0;
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_type_3918_) {
                4 => {
                    v_declName_3922_ = leanh::lean_ctor_get(v_type_3918_, 0);
                    leanh::lean_inc(v_declName_3922_);
                    leanh::lean_dec_ref_known(v_type_3918_, 2);
                    v___x_3923_ = l_Lean_Compiler_LCNF_toImpureType___closed__0;
                    v___x_3924_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_3922_, v___x_3923_, v_a_3919_, v_a_3920_);
                    return v___x_3924_;
                }
                5 => {
                    v___x_3925_ = l_Lean_Expr_getAppFn(v_type_3918_);
                    if leanh::lean_obj_tag(v___x_3925_) == 4 {
                        v_declName_3926_ = leanh::lean_ctor_get(v___x_3925_, 0);
                        leanh::lean_inc(v_declName_3926_);
                        leanh::lean_dec_ref_known(v___x_3925_, 2);
                        v_dummy_3927_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toImpureType___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_toImpureType___closed__1_once
                            ),
                            _init_l_Lean_Compiler_LCNF_toImpureType___closed__1,
                        );
                        v_nargs_3928_ = l_Lean_Expr_getAppNumArgs(v_type_3918_);
                        leanh::lean_inc(v_nargs_3928_);
                        v___x_3929_ = lean_mk_array(v_nargs_3928_, v_dummy_3927_);
                        v___x_3930_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3931_ = lean_nat_sub(v_nargs_3928_, v___x_3930_);
                        leanh::lean_dec(v_nargs_3928_);
                        v___x_3932_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v_type_3918_,
                            v___x_3929_,
                            v___x_3931_,
                        );
                        v___x_3933_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(v_declName_3926_, v___x_3932_, v_a_3919_, v_a_3920_);
                        return v___x_3933_;
                    } else {
                        leanh::lean_dec_ref_known(v_type_3918_, 2);
                        leanh::lean_dec_ref(v___x_3925_);
                        v___x_3934_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toImpureType___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_toImpureType___closed__3_once
                            ),
                            _init_l_Lean_Compiler_LCNF_toImpureType___closed__3,
                        );
                        v___x_3935_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(
                            v___x_3934_,
                            v_a_3919_,
                            v_a_3920_,
                        );
                        return v___x_3935_;
                    }
                }
                7 => {
                    v_body_3936_ = leanh::lean_ctor_get(v_type_3918_, 2);
                    leanh::lean_inc_ref(v_body_3936_);
                    leanh::lean_dec_ref_known(v_type_3918_, 3);
                    v___x_3937_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_isAnyProducingType(v_body_3936_);
                    leanh::lean_dec_ref(v_body_3936_);
                    if v___x_3937_ == 0 {
                        v___x_3938_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__5_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__5);
                        v___x_3939_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3939_, 0, v___x_3938_);
                        return v___x_3939_;
                    } else {
                        v___x_3940_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__2);
                        v___x_3941_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3941_, 0, v___x_3940_);
                        return v___x_3941_;
                    }
                }
                10 => {
                    v_expr_3942_ = leanh::lean_ctor_get(v_type_3918_, 1);
                    leanh::lean_inc_ref(v_expr_3942_);
                    leanh::lean_dec_ref_known(v_type_3918_, 2);
                    v_type_3918_ = v_expr_3942_;
                    state = 0;
                    continue;
                }
                _ => {
                    leanh::lean_dec_ref(v_type_3918_);
                    v___x_3944_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toImpureType___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_toImpureType___closed__4_once),
                        _init_l_Lean_Compiler_LCNF_toImpureType___closed__4,
                    );
                    v___x_3945_ = l_panic___at___00Lean_Compiler_LCNF_toImpureType_spec__1(
                        v___x_3944_,
                        v_a_3919_,
                        v_a_3920_,
                    );
                    return v___x_3945_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(
    mut v_declName_3946_: *mut leanh::LeanObject,
    mut v_args_3947_: *mut leanh::LeanObject,
    mut v_a_3948_: *mut leanh::LeanObject,
    mut v_a_3949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldIdx_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3975_: u8 = 0;
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3979_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_3946_);
                v___x_3951_ = l_Lean_Compiler_LCNF_hasTrivialImpureStructure_x3f(
                    v_declName_3946_,
                    v_a_3948_,
                    v_a_3949_,
                );
                if leanh::lean_obj_tag(v___x_3951_) == 0 {
                    v_a_3952_ = leanh::lean_ctor_get(v___x_3951_, 0);
                    leanh::lean_inc(v_a_3952_);
                    leanh::lean_dec_ref_known(v___x_3951_, 1);
                    if leanh::lean_obj_tag(v_a_3952_) == 1 {
                        leanh::lean_dec(v_declName_3946_);
                        v_val_3953_ = leanh::lean_ctor_get(v_a_3952_, 0);
                        leanh::lean_inc(v_val_3953_);
                        leanh::lean_dec_ref_known(v_a_3952_, 1);
                        v_ctorName_3954_ = leanh::lean_ctor_get(v_val_3953_, 0);
                        leanh::lean_inc(v_ctorName_3954_);
                        v_numParams_3955_ = leanh::lean_ctor_get(v_val_3953_, 1);
                        leanh::lean_inc(v_numParams_3955_);
                        v_fieldIdx_3956_ = leanh::lean_ctor_get(v_val_3953_, 2);
                        leanh::lean_inc(v_fieldIdx_3956_);
                        leanh::lean_dec(v_val_3953_);
                        v___x_3957_ = leanh::lean_box(0);
                        v___x_3958_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(
                            v_ctorName_3954_,
                            v___x_3957_,
                            v_a_3948_,
                            v_a_3949_,
                        );
                        if leanh::lean_obj_tag(v___x_3958_) == 0 {
                            v_a_3959_ = leanh::lean_ctor_get(v___x_3958_, 0);
                            leanh::lean_inc(v_a_3959_);
                            leanh::lean_dec_ref_known(v___x_3958_, 1);
                            v___x_3960_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3961_ = l_Array_toSubarray___redArg(
                                v_args_3947_,
                                v___x_3960_,
                                v_numParams_3955_,
                            );
                            v___x_3962_ = l_Subarray_copy___redArg(v___x_3961_);
                            v___x_3963_ = l_Lean_Compiler_LCNF_instantiateForall(
                                v_a_3959_,
                                v___x_3962_,
                                v_a_3948_,
                                v_a_3949_,
                            );
                            leanh::lean_dec_ref(v___x_3962_);
                            if leanh::lean_obj_tag(v___x_3963_) == 0 {
                                v_a_3964_ = leanh::lean_ctor_get(v___x_3963_, 0);
                                leanh::lean_inc(v_a_3964_);
                                leanh::lean_dec_ref_known(v___x_3963_, 1);
                                v___x_3965_ = l_Lean_instInhabitedExpr;
                                v___x_3966_ = l_Lean_Compiler_LCNF_getParamTypes(v_a_3964_);
                                v___x_3967_ =
                                    lean_array_get(v___x_3965_, v___x_3966_, v_fieldIdx_3956_);
                                leanh::lean_dec(v_fieldIdx_3956_);
                                leanh::lean_dec_ref(v___x_3966_);
                                v___x_3968_ = l_Lean_Compiler_LCNF_toMonoType(
                                    v___x_3967_,
                                    v_a_3948_,
                                    v_a_3949_,
                                );
                                if leanh::lean_obj_tag(v___x_3968_) == 0 {
                                    v_a_3969_ = leanh::lean_ctor_get(v___x_3968_, 0);
                                    leanh::lean_inc(v_a_3969_);
                                    leanh::lean_dec_ref_known(v___x_3968_, 1);
                                    v___x_3970_ = l_Lean_Compiler_LCNF_toImpureType(
                                        v_a_3969_, v_a_3948_, v_a_3949_,
                                    );
                                    return v___x_3970_;
                                } else {
                                    return v___x_3968_;
                                }
                            } else {
                                leanh::lean_dec(v_fieldIdx_3956_);
                                return v___x_3963_;
                            }
                        } else {
                            leanh::lean_dec(v_fieldIdx_3956_);
                            leanh::lean_dec(v_numParams_3955_);
                            leanh::lean_dec_ref(v_args_3947_);
                            return v___x_3958_;
                        }
                    } else {
                        leanh::lean_dec(v_a_3952_);
                        leanh::lean_dec_ref(v_args_3947_);
                        v___x_3971_ = l_Lean_Compiler_LCNF_nameToImpureType(
                            v_declName_3946_,
                            v_a_3948_,
                            v_a_3949_,
                        );
                        return v___x_3971_;
                    }
                } else {
                    leanh::lean_dec_ref(v_args_3947_);
                    leanh::lean_dec(v_declName_3946_);
                    v_a_3972_ = leanh::lean_ctor_get(v___x_3951_, 0);
                    v_isSharedCheck_3979_ = (!leanh::lean_is_exclusive(v___x_3951_)) as u8;
                    if v_isSharedCheck_3979_ == 0 {
                        v___x_3974_ = v___x_3951_;
                        v_isShared_3975_ = v_isSharedCheck_3979_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3972_);
                        leanh::lean_dec(v___x_3951_);
                        v___x_3974_ = leanh::lean_box(0);
                        v_isShared_3975_ = v_isSharedCheck_3979_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3975_ == 0 {
                    v___x_3977_ = v___x_3974_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3978_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
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
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp___boxed(
    mut v_declName_3980_: *mut leanh::LeanObject,
    mut v_args_3981_: *mut leanh::LeanObject,
    mut v_a_3982_: *mut leanh::LeanObject,
    mut v_a_3983_: *mut leanh::LeanObject,
    mut v_a_3984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3985_ =
        l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_toImpureType_visitApp(
            v_declName_3980_,
            v_args_3981_,
            v_a_3982_,
            v_a_3983_,
        );
    leanh::lean_dec(v_a_3983_);
    leanh::lean_dec_ref(v_a_3982_);
    return v_res_3985_;
}
pub unsafe fn l_Lean_Compiler_LCNF_toImpureType___boxed(
    mut v_type_3986_: *mut leanh::LeanObject,
    mut v_a_3987_: *mut leanh::LeanObject,
    mut v_a_3988_: *mut leanh::LeanObject,
    mut v_a_3989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3990_ = l_Lean_Compiler_LCNF_toImpureType(v_type_3986_, v_a_3987_, v_a_3988_);
    leanh::lean_dec(v_a_3988_);
    leanh::lean_dec_ref(v_a_3987_);
    return v_res_3990_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx(
    mut v_x_3991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3991_) {
        0 => {
            let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3992_ = leanh::lean_unsigned_to_nat(0);
            return v___x_3992_;
        }
        1 => {
            let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3993_ = leanh::lean_unsigned_to_nat(1);
            return v___x_3993_;
        }
        2 => {
            let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3994_ = leanh::lean_unsigned_to_nat(2);
            return v___x_3994_;
        }
        3 => {
            let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3995_ = leanh::lean_unsigned_to_nat(3);
            return v___x_3995_;
        }
        _ => {
            let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3996_ = leanh::lean_unsigned_to_nat(4);
            return v___x_3996_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx___boxed(
    mut v_x_3997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3998_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorIdx(v_x_3997_);
    leanh::lean_dec(v_x_3997_);
    return v_res_3998_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(
    mut v_t_3999_: *mut leanh::LeanObject,
    mut v_k_4000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_3999_) {
        1 => {
            let mut v_i_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_4001_ = leanh::lean_ctor_get(v_t_3999_, 0);
            leanh::lean_inc(v_i_4001_);
            v_type_4002_ = leanh::lean_ctor_get(v_t_3999_, 1);
            leanh::lean_inc_ref(v_type_4002_);
            leanh::lean_dec_ref_known(v_t_3999_, 2);
            v___x_4003_ = leanh::lean_apply_2(v_k_4000_, v_i_4001_, v_type_4002_);
            return v___x_4003_;
        }
        2 => {
            let mut v_i_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_4004_ = leanh::lean_ctor_get(v_t_3999_, 0);
            leanh::lean_inc(v_i_4004_);
            leanh::lean_dec_ref_known(v_t_3999_, 1);
            v___x_4005_ = leanh::lean_apply_1(v_k_4000_, v_i_4004_);
            return v___x_4005_;
        }
        3 => {
            let mut v_sz_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_offset_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_type_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_sz_4006_ = leanh::lean_ctor_get(v_t_3999_, 0);
            leanh::lean_inc(v_sz_4006_);
            v_offset_4007_ = leanh::lean_ctor_get(v_t_3999_, 1);
            leanh::lean_inc(v_offset_4007_);
            v_type_4008_ = leanh::lean_ctor_get(v_t_3999_, 2);
            leanh::lean_inc_ref(v_type_4008_);
            leanh::lean_dec_ref_known(v_t_3999_, 3);
            v___x_4009_ =
                leanh::lean_apply_3(v_k_4000_, v_sz_4006_, v_offset_4007_, v_type_4008_);
            return v___x_4009_;
        }
        _ => {
            leanh::lean_dec(v_t_3999_);
            return v_k_4000_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(
    mut v_motive_4010_: *mut leanh::LeanObject,
    mut v_ctorIdx_4011_: *mut leanh::LeanObject,
    mut v_t_4012_: *mut leanh::LeanObject,
    mut v_h_4013_: *mut leanh::LeanObject,
    mut v_k_4014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4015_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4012_, v_k_4014_);
    return v___x_4015_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___boxed(
    mut v_motive_4016_: *mut leanh::LeanObject,
    mut v_ctorIdx_4017_: *mut leanh::LeanObject,
    mut v_t_4018_: *mut leanh::LeanObject,
    mut v_h_4019_: *mut leanh::LeanObject,
    mut v_k_4020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4021_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim(
        v_motive_4016_,
        v_ctorIdx_4017_,
        v_t_4018_,
        v_h_4019_,
        v_k_4020_,
    );
    leanh::lean_dec(v_ctorIdx_4017_);
    return v_res_4021_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim___redArg(
    mut v_t_4022_: *mut leanh::LeanObject,
    mut v_erased_4023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4024_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4022_, v_erased_4023_);
    return v___x_4024_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_erased_elim(
    mut v_motive_4025_: *mut leanh::LeanObject,
    mut v_t_4026_: *mut leanh::LeanObject,
    mut v_h_4027_: *mut leanh::LeanObject,
    mut v_erased_4028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4029_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4026_, v_erased_4028_);
    return v___x_4029_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim___redArg(
    mut v_t_4030_: *mut leanh::LeanObject,
    mut v_object_4031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4032_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4030_, v_object_4031_);
    return v___x_4032_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_object_elim(
    mut v_motive_4033_: *mut leanh::LeanObject,
    mut v_t_4034_: *mut leanh::LeanObject,
    mut v_h_4035_: *mut leanh::LeanObject,
    mut v_object_4036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4037_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4034_, v_object_4036_);
    return v___x_4037_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim___redArg(
    mut v_t_4038_: *mut leanh::LeanObject,
    mut v_usize_4039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4040_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4038_, v_usize_4039_);
    return v___x_4040_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_usize_elim(
    mut v_motive_4041_: *mut leanh::LeanObject,
    mut v_t_4042_: *mut leanh::LeanObject,
    mut v_h_4043_: *mut leanh::LeanObject,
    mut v_usize_4044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4045_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4042_, v_usize_4044_);
    return v___x_4045_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim___redArg(
    mut v_t_4046_: *mut leanh::LeanObject,
    mut v_scalar_4047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4048_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4046_, v_scalar_4047_);
    return v___x_4048_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_scalar_elim(
    mut v_motive_4049_: *mut leanh::LeanObject,
    mut v_t_4050_: *mut leanh::LeanObject,
    mut v_h_4051_: *mut leanh::LeanObject,
    mut v_scalar_4052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4053_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4050_, v_scalar_4052_);
    return v___x_4053_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim___redArg(
    mut v_t_4054_: *mut leanh::LeanObject,
    mut v_void_4055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4054_, v_void_4055_);
    return v___x_4056_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CtorFieldInfo_void_elim(
    mut v_motive_4057_: *mut leanh::LeanObject,
    mut v_t_4058_: *mut leanh::LeanObject,
    mut v_h_4059_: *mut leanh::LeanObject,
    mut v_void_4060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4061_ = l_Lean_Compiler_LCNF_CtorFieldInfo_ctorElim___redArg(v_t_4058_, v_void_4060_);
    return v___x_4061_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default()
-> *mut leanh::LeanObject {
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4062_ = leanh::lean_box(0);
    return v___x_4062_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo()
-> *mut leanh::LeanObject {
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4063_ = leanh::lean_box(0);
    return v___x_4063_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format(
    mut v_x_4085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4103_: u8 = 0;
    let mut v_i_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4107_: u8 = 0;
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4114_: u8 = 0;
    let mut v_sz_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4085_) {
                0 => {
                    v___x_4086_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__1;
                    return v___x_4086_;
                }
                1 => {
                    v_i_4087_ = leanh::lean_ctor_get(v_x_4085_, 0);
                    v_type_4088_ = leanh::lean_ctor_get(v_x_4085_, 1);
                    v_isSharedCheck_4103_ = (!leanh::lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4103_ == 0 {
                        v___x_4090_ = v_x_4085_;
                        v_isShared_4091_ = v_isSharedCheck_4103_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_type_4088_);
                        leanh::lean_inc(v_i_4087_);
                        leanh::lean_dec(v_x_4085_);
                        v___x_4090_ = leanh::lean_box(0);
                        v_isShared_4091_ = v_isSharedCheck_4103_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_i_4104_ = leanh::lean_ctor_get(v_x_4085_, 0);
                    v_isSharedCheck_4114_ = (!leanh::lean_is_exclusive(v_x_4085_)) as u8;
                    if v_isSharedCheck_4114_ == 0 {
                        v___x_4106_ = v_x_4085_;
                        v_isShared_4107_ = v_isSharedCheck_4114_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_i_4104_);
                        leanh::lean_dec(v_x_4085_);
                        v___x_4106_ = leanh::lean_box(0);
                        v_isShared_4107_ = v_isSharedCheck_4114_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_sz_4115_ = leanh::lean_ctor_get(v_x_4085_, 0);
                    leanh::lean_inc(v_sz_4115_);
                    v_offset_4116_ = leanh::lean_ctor_get(v_x_4085_, 1);
                    leanh::lean_inc(v_offset_4116_);
                    v_type_4117_ = leanh::lean_ctor_get(v_x_4085_, 2);
                    leanh::lean_inc_ref(v_type_4117_);
                    leanh::lean_dec_ref_known(v_x_4085_, 3);
                    v___x_4118_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__9;
                    v___x_4119_ = l_Nat_reprFast(v_sz_4115_);
                    v___x_4120_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4120_, 0, v___x_4119_);
                    v___x_4121_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4121_, 0, v___x_4118_);
                    leanh::lean_ctor_set(v___x_4121_, 1, v___x_4120_);
                    v___x_4122_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__11;
                    v___x_4123_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4123_, 0, v___x_4121_);
                    leanh::lean_ctor_set(v___x_4123_, 1, v___x_4122_);
                    v___x_4124_ = l_Nat_reprFast(v_offset_4116_);
                    v___x_4125_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4125_, 0, v___x_4124_);
                    v___x_4126_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4126_, 0, v___x_4123_);
                    leanh::lean_ctor_set(v___x_4126_, 1, v___x_4125_);
                    v___x_4127_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5;
                    v___x_4128_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4128_, 0, v___x_4126_);
                    leanh::lean_ctor_set(v___x_4128_, 1, v___x_4127_);
                    v___x_4129_ = lean_expr_dbg_to_string(v_type_4117_);
                    leanh::lean_dec_ref(v_type_4117_);
                    v___x_4130_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4130_, 0, v___x_4129_);
                    v___x_4131_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4131_, 0, v___x_4128_);
                    leanh::lean_ctor_set(v___x_4131_, 1, v___x_4130_);
                    return v___x_4131_;
                }
                _ => {
                    v___x_4132_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__13;
                    return v___x_4132_;
                }
            },
            1 => {
                v___x_4092_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__3;
                v___x_4093_ = l_Nat_reprFast(v_i_4087_);
                v___x_4094_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4094_, 0, v___x_4093_);
                if v_isShared_4091_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4090_, 5);
                    leanh::lean_ctor_set(v___x_4090_, 1, v___x_4094_);
                    leanh::lean_ctor_set(v___x_4090_, 0, v___x_4092_);
                    v___x_4096_ = v___x_4090_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4102_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4102_, 1, v___x_4094_);
                    v___x_4096_ = v_reuseFailAlloc_4102_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4097_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__5;
                v___x_4098_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4098_, 0, v___x_4096_);
                leanh::lean_ctor_set(v___x_4098_, 1, v___x_4097_);
                v___x_4099_ = lean_expr_dbg_to_string(v_type_4088_);
                leanh::lean_dec_ref(v_type_4088_);
                v___x_4100_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4100_, 0, v___x_4099_);
                v___x_4101_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4101_, 0, v___x_4098_);
                leanh::lean_ctor_set(v___x_4101_, 1, v___x_4100_);
                return v___x_4101_;
            }
            3 => {
                v___x_4108_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_CtorFieldInfo_format___closed__7;
                v___x_4109_ = l_Nat_reprFast(v_i_4104_);
                if v_isShared_4107_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4106_, 3);
                    leanh::lean_ctor_set(v___x_4106_, 0, v___x_4109_);
                    v___x_4111_ = v___x_4106_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4109_);
                    v___x_4111_ = v_reuseFailAlloc_4113_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4112_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4112_, 0, v___x_4108_);
                leanh::lean_ctor_set(v___x_4112_, 1, v___x_4111_);
                return v___x_4112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__0;
    v___x_4138_ = l_Lean_Compiler_LCNF_instInhabitedCtorInfo_default;
    v___x_4139_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4139_, 0, v___x_4138_);
    leanh::lean_ctor_set(v___x_4139_, 1, v___x_4137_);
    return v___x_4139_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default()
-> *mut leanh::LeanObject {
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1_once
        ),
        _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default___closed__1,
    );
    return v___x_4140_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout() -> *mut leanh::LeanObject
{
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4141_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
    return v___x_4141_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msg_4142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4143_ = l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default;
    v___x_4144_ = lean_panic_fn_borrowed(v___x_4143_, v_msg_4142_);
    return v___x_4144_;
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0_spec__1(
    mut v_newState_4145_: *mut leanh::LeanObject,
    mut v_x_4146_: *mut leanh::LeanObject,
    mut v_x_4147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v_fst_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4157_: u8 = 0;
    let mut v_snd_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4173_: u8 = 0;
    let mut v_isSharedCheck_4174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4147_) == 0 {
                    return v_x_4146_;
                } else {
                    v_head_4148_ = leanh::lean_ctor_get(v_x_4147_, 0);
                    v_tail_4149_ = leanh::lean_ctor_get(v_x_4147_, 1);
                    v_isSharedCheck_4174_ = (!leanh::lean_is_exclusive(v_x_4147_)) as u8;
                    if v_isSharedCheck_4174_ == 0 {
                        v___x_4151_ = v_x_4147_;
                        v_isShared_4152_ = v_isSharedCheck_4174_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4149_);
                        leanh::lean_inc(v_head_4148_);
                        leanh::lean_dec(v_x_4147_);
                        v___x_4151_ = leanh::lean_box(0);
                        v_isShared_4152_ = v_isSharedCheck_4174_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4153_ = leanh::lean_ctor_get(v_x_4146_, 0);
                v_snd_4154_ = leanh::lean_ctor_get(v_x_4146_, 1);
                v_isSharedCheck_4173_ = (!leanh::lean_is_exclusive(v_x_4146_)) as u8;
                if v_isSharedCheck_4173_ == 0 {
                    v___x_4156_ = v_x_4146_;
                    v_isShared_4157_ = v_isSharedCheck_4173_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4154_);
                    leanh::lean_inc(v_fst_4153_);
                    leanh::lean_dec(v_x_4146_);
                    v___x_4156_ = leanh::lean_box(0);
                    v_isShared_4157_ = v_isSharedCheck_4173_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_4158_ = leanh::lean_ctor_get(v_newState_4145_, 1);
                leanh::lean_inc(v_head_4148_);
                if v_isShared_4152_ == 0 {
                    leanh::lean_ctor_set(v___x_4151_, 1, v_fst_4153_);
                    v___x_4160_ = v___x_4151_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4172_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_head_4148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4172_, 1, v_fst_4153_);
                    v___x_4160_ = v_reuseFailAlloc_4172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4168_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_4158_, v_head_4148_);
                if leanh::lean_obj_tag(v___x_4168_) == 0 {
                    v___x_4169_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__3___closed__3);
                    v___x_4170_ = l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0_spec__0(v___x_4169_);
                    v___y_4162_ = v___x_4170_;
                    state = 4;
                    continue;
                } else {
                    v_val_4171_ = leanh::lean_ctor_get(v___x_4168_, 0);
                    leanh::lean_inc(v_val_4171_);
                    leanh::lean_dec_ref_known(v___x_4168_, 1);
                    v___y_4162_ = v_val_4171_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4163_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_4154_, v_head_4148_, v___y_4162_);
                if v_isShared_4157_ == 0 {
                    leanh::lean_ctor_set(v___x_4156_, 1, v___x_4163_);
                    leanh::lean_ctor_set(v___x_4156_, 0, v___x_4160_);
                    v___x_4165_ = v___x_4156_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4167_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4160_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 1, v___x_4163_);
                    v___x_4165_ = v_reuseFailAlloc_4167_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_x_4146_ = v___x_4165_;
                v_x_4147_ = v_tail_4149_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_newState_4175_: *mut leanh::LeanObject,
    mut v_x_4176_: *mut leanh::LeanObject,
    mut v_x_4177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4178_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0_spec__1(v_newState_4175_, v_x_4176_, v_x_4177_);
    leanh::lean_dec_ref(v_newState_4175_);
    return v_res_4178_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___lam__0(
    mut v_oldState_4179_: *mut leanh::LeanObject,
    mut v_newState_4180_: *mut leanh::LeanObject,
    mut v_x_4181_: *mut leanh::LeanObject,
    mut v_s_4182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_4183_ = leanh::lean_ctor_get(v_newState_4180_, 0);
    v_fst_4184_ = leanh::lean_ctor_get(v_oldState_4179_, 0);
    v___x_4185_ = l_List_lengthTR___redArg(v_fst_4183_);
    v___x_4186_ = l_List_lengthTR___redArg(v_fst_4184_);
    v___x_4187_ = lean_nat_sub(v___x_4185_, v___x_4186_);
    leanh::lean_dec(v___x_4186_);
    leanh::lean_dec(v___x_4185_);
    v___x_4188_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0___lam__0___closed__0;
    leanh::lean_inc(v_fst_4183_);
    v_newEntries_4189_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        leanh::lean_box(0),
        v_fst_4183_,
        v_fst_4183_,
        v___x_4187_,
        v___x_4188_,
    );
    v___x_4190_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0_spec__1(v_newState_4180_, v_s_4182_, v_newEntries_4189_);
    leanh::lean_dec_ref(v_newState_4180_);
    return v___x_4190_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___lam__0___boxed(
    mut v_oldState_4191_: *mut leanh::LeanObject,
    mut v_newState_4192_: *mut leanh::LeanObject,
    mut v_x_4193_: *mut leanh::LeanObject,
    mut v_s_4194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4195_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___lam__0(v_oldState_4191_, v_newState_4192_, v_x_4193_, v_s_4194_);
    leanh::lean_dec(v_x_4193_);
    leanh::lean_dec_ref(v_oldState_4191_);
    return v_res_4195_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___lam__1(
    mut v___x_4196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4198_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4198_, 0, v___x_4196_);
    return v___x_4198_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___lam__1___boxed(
    mut v___x_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4201_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___lam__1(v___x_4199_);
    return v_res_4201_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4203_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4203_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4204_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__1);
    v___x_4205_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4205_, 0, v___x_4204_);
    return v___x_4205_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4206_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__2);
    v___x_4207_ = leanh::lean_box(0);
    v___x_4208_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4208_, 0, v___x_4207_);
    leanh::lean_ctor_set(v___x_4208_, 1, v___x_4206_);
    return v___x_4208_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4209_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__3);
    v___f_4210_ = leanh::lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_4210_, 0, v___x_4209_);
    return v___f_4210_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0()
-> *mut leanh::LeanObject {
    let mut v___f_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4221_: u8 = 0;
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4225_: u8 = 0;
    let mut v_a_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4214_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__4_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__4);
                v___x_4215_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___closed__5;
                v___x_4216_ = leanh::lean_box(0);
                v___x_4217_ =
                    l_Lean_registerEnvExtension___redArg(v___f_4214_, v___x_4215_, v___x_4216_);
                if leanh::lean_obj_tag(v___x_4217_) == 0 {
                    v_a_4218_ = leanh::lean_ctor_get(v___x_4217_, 0);
                    v_isSharedCheck_4225_ = (!leanh::lean_is_exclusive(v___x_4217_)) as u8;
                    if v_isSharedCheck_4225_ == 0 {
                        v___x_4220_ = v___x_4217_;
                        v_isShared_4221_ = v_isSharedCheck_4225_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4218_);
                        leanh::lean_dec(v___x_4217_);
                        v___x_4220_ = leanh::lean_box(0);
                        v_isShared_4221_ = v_isSharedCheck_4225_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4226_ = leanh::lean_ctor_get(v___x_4217_, 0);
                    v_isSharedCheck_4233_ = (!leanh::lean_is_exclusive(v___x_4217_)) as u8;
                    if v_isSharedCheck_4233_ == 0 {
                        v___x_4228_ = v___x_4217_;
                        v_isShared_4229_ = v_isSharedCheck_4233_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4226_);
                        leanh::lean_dec(v___x_4217_);
                        v___x_4228_ = leanh::lean_box(0);
                        v_isShared_4229_ = v_isSharedCheck_4233_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4221_ == 0 {
                    v___x_4223_ = v___x_4220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4224_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
                    v___x_4223_ = v_reuseFailAlloc_4224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4223_;
            }
            3 => {
                if v_isShared_4229_ == 0 {
                    v___x_4231_ = v___x_4228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
                    v___x_4231_ = v_reuseFailAlloc_4232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0___boxed(
    mut v_a_4234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4235_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0();
    return v_res_4235_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4237_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2__spec__0();
    return v___x_4237_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2____boxed(
    mut v_a_4238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4239_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2_();
    return v_res_4239_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__1(
    mut v_msg_4240_: *mut leanh::LeanObject,
    mut v___y_4241_: *mut leanh::LeanObject,
    mut v___y_4242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11568__overap_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4244_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__0___closed__0;
    v___x_11568__overap_4245_ = lean_panic_fn_borrowed(v___f_4244_, v_msg_4240_);
    leanh::lean_inc(v___y_4242_);
    leanh::lean_inc_ref(v___y_4241_);
    v___x_4246_ = leanh::lean_apply_3(
        v___x_11568__overap_4245_,
        v___y_4241_,
        v___y_4242_,
        leanh::lean_box(0),
    );
    return v___x_4246_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__1___boxed(
    mut v_msg_4247_: *mut leanh::LeanObject,
    mut v___y_4248_: *mut leanh::LeanObject,
    mut v___y_4249_: *mut leanh::LeanObject,
    mut v___y_4250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4251_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__1(v_msg_4247_, v___y_4248_, v___y_4249_);
    leanh::lean_dec(v___y_4249_);
    leanh::lean_dec_ref(v___y_4248_);
    return v_res_4251_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__2(
    mut v_msg_4253_: *mut leanh::LeanObject,
    mut v___y_4254_: *mut leanh::LeanObject,
    mut v___y_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_11578__overap_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4259_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__2___closed__0;
    v___x_11578__overap_4260_ = lean_panic_fn_borrowed(v___f_4259_, v_msg_4253_);
    leanh::lean_inc(v___y_4257_);
    leanh::lean_inc_ref(v___y_4256_);
    leanh::lean_inc(v___y_4255_);
    leanh::lean_inc_ref(v___y_4254_);
    v___x_4261_ = leanh::lean_apply_5(
        v___x_11578__overap_4260_,
        v___y_4254_,
        v___y_4255_,
        v___y_4256_,
        v___y_4257_,
        leanh::lean_box(0),
    );
    return v___x_4261_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__2___boxed(
    mut v_msg_4262_: *mut leanh::LeanObject,
    mut v___y_4263_: *mut leanh::LeanObject,
    mut v___y_4264_: *mut leanh::LeanObject,
    mut v___y_4265_: *mut leanh::LeanObject,
    mut v___y_4266_: *mut leanh::LeanObject,
    mut v___y_4267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4268_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__2(v_msg_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
    leanh::lean_dec(v___y_4266_);
    leanh::lean_dec_ref(v___y_4265_);
    leanh::lean_dec(v___y_4264_);
    leanh::lean_dec_ref(v___y_4263_);
    return v_res_4268_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__5___redArg(
    mut v_type_4269_: *mut leanh::LeanObject,
    mut v_k_4270_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4271_: u8,
    mut v_whnfType_4272_: u8,
    mut v___y_4273_: *mut leanh::LeanObject,
    mut v___y_4274_: *mut leanh::LeanObject,
    mut v___y_4275_: *mut leanh::LeanObject,
    mut v___y_4276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4283_: u8 = 0;
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4287_: u8 = 0;
    let mut v_a_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4291_: u8 = 0;
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4278_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_4278_, 0, v_k_4270_);
                v___x_4279_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    leanh::lean_box(0),
                    v_type_4269_,
                    v___f_4278_,
                    v_cleanupAnnotations_4271_,
                    v_whnfType_4272_,
                    v___y_4273_,
                    v___y_4274_,
                    v___y_4275_,
                    v___y_4276_,
                );
                if leanh::lean_obj_tag(v___x_4279_) == 0 {
                    v_a_4280_ = leanh::lean_ctor_get(v___x_4279_, 0);
                    v_isSharedCheck_4287_ = (!leanh::lean_is_exclusive(v___x_4279_)) as u8;
                    if v_isSharedCheck_4287_ == 0 {
                        v___x_4282_ = v___x_4279_;
                        v_isShared_4283_ = v_isSharedCheck_4287_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4280_);
                        leanh::lean_dec(v___x_4279_);
                        v___x_4282_ = leanh::lean_box(0);
                        v_isShared_4283_ = v_isSharedCheck_4287_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4288_ = leanh::lean_ctor_get(v___x_4279_, 0);
                    v_isSharedCheck_4295_ = (!leanh::lean_is_exclusive(v___x_4279_)) as u8;
                    if v_isSharedCheck_4295_ == 0 {
                        v___x_4290_ = v___x_4279_;
                        v_isShared_4291_ = v_isSharedCheck_4295_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4288_);
                        leanh::lean_dec(v___x_4279_);
                        v___x_4290_ = leanh::lean_box(0);
                        v_isShared_4291_ = v_isSharedCheck_4295_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4283_ == 0 {
                    v___x_4285_ = v___x_4282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4286_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
                    v___x_4285_ = v_reuseFailAlloc_4286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4285_;
            }
            3 => {
                if v_isShared_4291_ == 0 {
                    v___x_4293_ = v___x_4290_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4294_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_a_4288_);
                    v___x_4293_ = v_reuseFailAlloc_4294_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__5___redArg___boxed(
    mut v_type_4296_: *mut leanh::LeanObject,
    mut v_k_4297_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4298_: *mut leanh::LeanObject,
    mut v_whnfType_4299_: *mut leanh::LeanObject,
    mut v___y_4300_: *mut leanh::LeanObject,
    mut v___y_4301_: *mut leanh::LeanObject,
    mut v___y_4302_: *mut leanh::LeanObject,
    mut v___y_4303_: *mut leanh::LeanObject,
    mut v___y_4304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4305_: u8 = 0;
    let mut v_whnfType_boxed_4306_: u8 = 0;
    let mut v_res_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4305_ = (leanh::lean_unbox(v_cleanupAnnotations_4298_) as u8);
    v_whnfType_boxed_4306_ = (leanh::lean_unbox(v_whnfType_4299_) as u8);
    v_res_4307_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__5___redArg(v_type_4296_, v_k_4297_, v_cleanupAnnotations_boxed_4305_, v_whnfType_boxed_4306_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
    leanh::lean_dec(v___y_4303_);
    leanh::lean_dec_ref(v___y_4302_);
    leanh::lean_dec(v___y_4301_);
    leanh::lean_dec_ref(v___y_4300_);
    return v_res_4307_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__5(
    mut v_00_u03b1_4308_: *mut leanh::LeanObject,
    mut v_type_4309_: *mut leanh::LeanObject,
    mut v_k_4310_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4311_: u8,
    mut v_whnfType_4312_: u8,
    mut v___y_4313_: *mut leanh::LeanObject,
    mut v___y_4314_: *mut leanh::LeanObject,
    mut v___y_4315_: *mut leanh::LeanObject,
    mut v___y_4316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4318_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__5___redArg(v_type_4309_, v_k_4310_, v_cleanupAnnotations_4311_, v_whnfType_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
    return v___x_4318_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__5___boxed(
    mut v_00_u03b1_4319_: *mut leanh::LeanObject,
    mut v_type_4320_: *mut leanh::LeanObject,
    mut v_k_4321_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4322_: *mut leanh::LeanObject,
    mut v_whnfType_4323_: *mut leanh::LeanObject,
    mut v___y_4324_: *mut leanh::LeanObject,
    mut v___y_4325_: *mut leanh::LeanObject,
    mut v___y_4326_: *mut leanh::LeanObject,
    mut v___y_4327_: *mut leanh::LeanObject,
    mut v___y_4328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4329_: u8 = 0;
    let mut v_whnfType_boxed_4330_: u8 = 0;
    let mut v_res_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4329_ = (leanh::lean_unbox(v_cleanupAnnotations_4322_) as u8);
    v_whnfType_boxed_4330_ = (leanh::lean_unbox(v_whnfType_4323_) as u8);
    v_res_4331_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__5(v_00_u03b1_4319_, v_type_4320_, v_k_4321_, v_cleanupAnnotations_boxed_4329_, v_whnfType_boxed_4330_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
    leanh::lean_dec(v___y_4327_);
    leanh::lean_dec_ref(v___y_4326_);
    leanh::lean_dec(v___y_4325_);
    leanh::lean_dec_ref(v___y_4324_);
    return v_res_4331_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__0(
    mut v_size_4332_: *mut leanh::LeanObject,
    mut v_sz_4333_: usize,
    mut v_i_4334_: usize,
    mut v_bs_4335_: *mut leanh::LeanObject,
    mut v___y_4336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4337_: u8 = 0;
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: usize = 0;
    let mut v___x_4346_: usize = 0;
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: u8 = 0;
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4354_: u8 = 0;
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4359_: u8 = 0;
    let mut v_unused_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4337_ = lean_usize_dec_lt(v_i_4334_, v_sz_4333_);
                if v___x_4337_ == 0 {
                    v___x_4338_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4338_, 0, v_bs_4335_);
                    leanh::lean_ctor_set(v___x_4338_, 1, v___y_4336_);
                    return v___x_4338_;
                } else {
                    v_v_4339_ = lean_array_uget(v_bs_4335_, v_i_4334_);
                    v___x_4340_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4341_ = lean_array_uset(v_bs_4335_, v_i_4334_, v___x_4340_);
                    match leanh::lean_obj_tag(v_v_4339_) {
                        1 => {
                            v_fst_4343_ = v_v_4339_;
                            v_snd_4344_ = v___y_4336_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_fst_4343_ = v_v_4339_;
                            v_snd_4344_ = v___y_4336_;
                            state = 1;
                            continue;
                        }
                        3 => {
                            v_sz_4349_ = leanh::lean_ctor_get(v_v_4339_, 0);
                            v_type_4350_ = leanh::lean_ctor_get(v_v_4339_, 2);
                            v___x_4351_ = lean_nat_dec_eq(v_sz_4349_, v_size_4332_);
                            if v___x_4351_ == 0 {
                                v_fst_4343_ = v_v_4339_;
                                v_snd_4344_ = v___y_4336_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc_ref(v_type_4350_);
                                leanh::lean_inc(v_sz_4349_);
                                v_isSharedCheck_4359_ =
                                    (!leanh::lean_is_exclusive(v_v_4339_)) as u8;
                                if v_isSharedCheck_4359_ == 0 {
                                    v_unused_4360_ = leanh::lean_ctor_get(v_v_4339_, 2);
                                    leanh::lean_dec(v_unused_4360_);
                                    v_unused_4361_ = leanh::lean_ctor_get(v_v_4339_, 1);
                                    leanh::lean_dec(v_unused_4361_);
                                    v_unused_4362_ = leanh::lean_ctor_get(v_v_4339_, 0);
                                    leanh::lean_dec(v_unused_4362_);
                                    v___x_4353_ = v_v_4339_;
                                    v_isShared_4354_ = v_isSharedCheck_4359_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_v_4339_);
                                    v___x_4353_ = leanh::lean_box(0);
                                    v_isShared_4354_ = v_isSharedCheck_4359_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            v_fst_4343_ = v_v_4339_;
                            v_snd_4344_ = v___y_4336_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4345_ = 1usize;
                v___x_4346_ = lean_usize_add(v_i_4334_, v___x_4345_);
                v___x_4347_ = lean_array_uset(v_bs_x27_4341_, v_i_4334_, v_fst_4343_);
                v_i_4334_ = v___x_4346_;
                v_bs_4335_ = v___x_4347_;
                v___y_4336_ = v_snd_4344_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4355_ = lean_nat_add(v___y_4336_, v_sz_4349_);
                if v_isShared_4354_ == 0 {
                    leanh::lean_ctor_set(v___x_4353_, 1, v___y_4336_);
                    v___x_4357_ = v___x_4353_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4358_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_sz_4349_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4358_, 1, v___y_4336_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4358_, 2, v_type_4350_);
                    v___x_4357_ = v_reuseFailAlloc_4358_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_4343_ = v___x_4357_;
                v_snd_4344_ = v___x_4355_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__0___boxed(
    mut v_size_4363_: *mut leanh::LeanObject,
    mut v_sz_4364_: *mut leanh::LeanObject,
    mut v_i_4365_: *mut leanh::LeanObject,
    mut v_bs_4366_: *mut leanh::LeanObject,
    mut v___y_4367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4368_: usize = 0;
    let mut v_i_boxed_4369_: usize = 0;
    let mut v_res_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4368_ = leanh::lean_unbox_usize(v_sz_4364_);
    leanh::lean_dec(v_sz_4364_);
    v_i_boxed_4369_ = leanh::lean_unbox_usize(v_i_4365_);
    leanh::lean_dec(v_i_4365_);
    v_res_4370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__0(v_size_4363_, v_sz_boxed_4368_, v_i_boxed_4369_, v_bs_4366_, v___y_4367_);
    leanh::lean_dec(v_size_4363_);
    return v_res_4370_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___lam__0(
    mut v_fields_4371_: *mut leanh::LeanObject,
    mut v_size_4372_: *mut leanh::LeanObject,
    mut v_nextOffset_4373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4374_: usize = 0;
    let mut v___x_4375_: usize = 0;
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4374_ = lean_array_size(v_fields_4371_);
    v___x_4375_ = 0usize;
    v___x_4376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__0(v_size_4372_, v_sz_4374_, v___x_4375_, v_fields_4371_, v_nextOffset_4373_);
    return v___x_4376_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___lam__0___boxed(
    mut v_fields_4377_: *mut leanh::LeanObject,
    mut v_size_4378_: *mut leanh::LeanObject,
    mut v_nextOffset_4379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4380_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___lam__0(v_fields_4377_, v_size_4378_, v_nextOffset_4379_);
    leanh::lean_dec(v_size_4378_);
    return v_res_4380_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(
    mut v_fst_4381_: *mut leanh::LeanObject,
    mut v_ctorField_4382_: *mut leanh::LeanObject,
    mut v_nextIdx_4383_: *mut leanh::LeanObject,
    mut v_has1BScalar_4384_: u8,
    mut v_has2BScalar_4385_: u8,
    mut v_has4BScalar_4386_: u8,
    mut v_has8BScalar_4387_: u8,
    mut v___y_4388_: *mut leanh::LeanObject,
    mut v___y_4389_: *mut leanh::LeanObject,
    mut v___y_4390_: *mut leanh::LeanObject,
    mut v___y_4391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4393_ = lean_array_push(v_fst_4381_, v_ctorField_4382_);
    v___x_4394_ = leanh::lean_box((v_has4BScalar_4386_) as usize);
    v___x_4395_ = leanh::lean_box((v_has8BScalar_4387_) as usize);
    v___x_4396_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4396_, 0, v___x_4394_);
    leanh::lean_ctor_set(v___x_4396_, 1, v___x_4395_);
    v___x_4397_ = leanh::lean_box((v_has2BScalar_4385_) as usize);
    v___x_4398_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4398_, 0, v___x_4397_);
    leanh::lean_ctor_set(v___x_4398_, 1, v___x_4396_);
    v___x_4399_ = leanh::lean_box((v_has1BScalar_4384_) as usize);
    v___x_4400_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4400_, 0, v___x_4399_);
    leanh::lean_ctor_set(v___x_4400_, 1, v___x_4398_);
    v___x_4401_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4401_, 0, v_nextIdx_4383_);
    leanh::lean_ctor_set(v___x_4401_, 1, v___x_4400_);
    v___x_4402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4402_, 0, v___x_4393_);
    leanh::lean_ctor_set(v___x_4402_, 1, v___x_4401_);
    v___x_4403_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4403_, 0, v___x_4402_);
    v___x_4404_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4404_, 0, v___x_4403_);
    return v___x_4404_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0___boxed(
    mut v_fst_4405_: *mut leanh::LeanObject,
    mut v_ctorField_4406_: *mut leanh::LeanObject,
    mut v_nextIdx_4407_: *mut leanh::LeanObject,
    mut v_has1BScalar_4408_: *mut leanh::LeanObject,
    mut v_has2BScalar_4409_: *mut leanh::LeanObject,
    mut v_has4BScalar_4410_: *mut leanh::LeanObject,
    mut v_has8BScalar_4411_: *mut leanh::LeanObject,
    mut v___y_4412_: *mut leanh::LeanObject,
    mut v___y_4413_: *mut leanh::LeanObject,
    mut v___y_4414_: *mut leanh::LeanObject,
    mut v___y_4415_: *mut leanh::LeanObject,
    mut v___y_4416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_has1BScalar_boxed_4417_: u8 = 0;
    let mut v_has2BScalar_boxed_4418_: u8 = 0;
    let mut v_has4BScalar_boxed_4419_: u8 = 0;
    let mut v_has8BScalar_boxed_4420_: u8 = 0;
    let mut v_res_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_has1BScalar_boxed_4417_ = (leanh::lean_unbox(v_has1BScalar_4408_) as u8);
    v_has2BScalar_boxed_4418_ = (leanh::lean_unbox(v_has2BScalar_4409_) as u8);
    v_has4BScalar_boxed_4419_ = (leanh::lean_unbox(v_has4BScalar_4410_) as u8);
    v_has8BScalar_boxed_4420_ = (leanh::lean_unbox(v_has8BScalar_4411_) as u8);
    v_res_4421_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_4405_, v_ctorField_4406_, v_nextIdx_4407_, v_has1BScalar_boxed_4417_, v_has2BScalar_boxed_4418_, v_has4BScalar_boxed_4419_, v_has8BScalar_boxed_4420_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
    leanh::lean_dec(v___y_4415_);
    leanh::lean_dec_ref(v___y_4414_);
    leanh::lean_dec(v___y_4413_);
    leanh::lean_dec_ref(v___y_4412_);
    return v_res_4421_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__2(
    mut v_fst_4422_: *mut leanh::LeanObject,
    mut v___x_4423_: *mut leanh::LeanObject,
    mut v_a_4424_: *mut leanh::LeanObject,
    mut v___f_4425_: *mut leanh::LeanObject,
    mut v_fst_4426_: *mut leanh::LeanObject,
    mut v_fst_4427_: *mut leanh::LeanObject,
    mut v_fst_4428_: *mut leanh::LeanObject,
    mut v_snd_4429_: *mut leanh::LeanObject,
    mut v_00___4430_: *mut leanh::LeanObject,
    mut v___y_4431_: *mut leanh::LeanObject,
    mut v___y_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
    mut v___y_4434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4436_ = lean_nat_add(v_fst_4422_, v___x_4423_);
    v___x_4437_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4437_, 0, v_fst_4422_);
    leanh::lean_ctor_set(v___x_4437_, 1, v_a_4424_);
    leanh::lean_inc(v___y_4434_);
    leanh::lean_inc_ref(v___y_4433_);
    leanh::lean_inc(v___y_4432_);
    leanh::lean_inc_ref(v___y_4431_);
    v___x_4438_ = leanh::lean_apply_11(
        v___f_4425_,
        v___x_4437_,
        v___x_4436_,
        v_fst_4426_,
        v_fst_4427_,
        v_fst_4428_,
        v_snd_4429_,
        v___y_4431_,
        v___y_4432_,
        v___y_4433_,
        v___y_4434_,
        leanh::lean_box(0),
    );
    return v___x_4438_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__2___boxed(
    mut v_fst_4439_: *mut leanh::LeanObject,
    mut v___x_4440_: *mut leanh::LeanObject,
    mut v_a_4441_: *mut leanh::LeanObject,
    mut v___f_4442_: *mut leanh::LeanObject,
    mut v_fst_4443_: *mut leanh::LeanObject,
    mut v_fst_4444_: *mut leanh::LeanObject,
    mut v_fst_4445_: *mut leanh::LeanObject,
    mut v_snd_4446_: *mut leanh::LeanObject,
    mut v_00___4447_: *mut leanh::LeanObject,
    mut v___y_4448_: *mut leanh::LeanObject,
    mut v___y_4449_: *mut leanh::LeanObject,
    mut v___y_4450_: *mut leanh::LeanObject,
    mut v___y_4451_: *mut leanh::LeanObject,
    mut v___y_4452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4453_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_4439_, v___x_4440_, v_a_4441_, v___f_4442_, v_fst_4443_, v_fst_4444_, v_fst_4445_, v_snd_4446_, v_00___4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
    leanh::lean_dec(v___y_4451_);
    leanh::lean_dec_ref(v___y_4450_);
    leanh::lean_dec(v___y_4449_);
    leanh::lean_dec_ref(v___y_4448_);
    leanh::lean_dec(v___x_4440_);
    return v_res_4453_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4455_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__2;
    v___x_4456_ = leanh::lean_unsigned_to_nat(13);
    v___x_4457_ = leanh::lean_unsigned_to_nat(202);
    v___x_4458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0;
    v___x_4459_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__0;
    v___x_4460_ = l_mkPanicMessageWithDecl(
        v___x_4459_,
        v___x_4458_,
        v___x_4457_,
        v___x_4456_,
        v___x_4455_,
    );
    return v___x_4460_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(
    mut v___f_4461_: *mut leanh::LeanObject,
    mut v_fst_4462_: *mut leanh::LeanObject,
    mut v_fst_4463_: *mut leanh::LeanObject,
    mut v_fst_4464_: *mut leanh::LeanObject,
    mut v_fst_4465_: *mut leanh::LeanObject,
    mut v_snd_4466_: *mut leanh::LeanObject,
    mut v_x_4467_: *mut leanh::LeanObject,
    mut v___y_4468_: *mut leanh::LeanObject,
    mut v___y_4469_: *mut leanh::LeanObject,
    mut v___y_4470_: *mut leanh::LeanObject,
    mut v___y_4471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4480_: u8 = 0;
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4473_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__1);
                v___x_4474_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__2(v___x_4473_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
                if leanh::lean_obj_tag(v___x_4474_) == 0 {
                    v_a_4475_ = leanh::lean_ctor_get(v___x_4474_, 0);
                    leanh::lean_inc(v_a_4475_);
                    leanh::lean_dec_ref_known(v___x_4474_, 1);
                    leanh::lean_inc(v___y_4471_);
                    leanh::lean_inc_ref(v___y_4470_);
                    leanh::lean_inc(v___y_4469_);
                    leanh::lean_inc_ref(v___y_4468_);
                    v___x_4476_ = leanh::lean_apply_11(
                        v___f_4461_,
                        v_a_4475_,
                        v_fst_4462_,
                        v_fst_4463_,
                        v_fst_4464_,
                        v_fst_4465_,
                        v_snd_4466_,
                        v___y_4468_,
                        v___y_4469_,
                        v___y_4470_,
                        v___y_4471_,
                        leanh::lean_box(0),
                    );
                    return v___x_4476_;
                } else {
                    leanh::lean_dec(v_snd_4466_);
                    leanh::lean_dec(v_fst_4465_);
                    leanh::lean_dec(v_fst_4464_);
                    leanh::lean_dec(v_fst_4463_);
                    leanh::lean_dec(v_fst_4462_);
                    leanh::lean_dec_ref(v___f_4461_);
                    v_a_4477_ = leanh::lean_ctor_get(v___x_4474_, 0);
                    v_isSharedCheck_4484_ = (!leanh::lean_is_exclusive(v___x_4474_)) as u8;
                    if v_isSharedCheck_4484_ == 0 {
                        v___x_4479_ = v___x_4474_;
                        v_isShared_4480_ = v_isSharedCheck_4484_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4477_);
                        leanh::lean_dec(v___x_4474_);
                        v___x_4479_ = leanh::lean_box(0);
                        v_isShared_4480_ = v_isSharedCheck_4484_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4480_ == 0 {
                    v___x_4482_ = v___x_4479_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
                    v___x_4482_ = v_reuseFailAlloc_4483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___boxed(
    mut v___f_4485_: *mut leanh::LeanObject,
    mut v_fst_4486_: *mut leanh::LeanObject,
    mut v_fst_4487_: *mut leanh::LeanObject,
    mut v_fst_4488_: *mut leanh::LeanObject,
    mut v_fst_4489_: *mut leanh::LeanObject,
    mut v_snd_4490_: *mut leanh::LeanObject,
    mut v_x_4491_: *mut leanh::LeanObject,
    mut v___y_4492_: *mut leanh::LeanObject,
    mut v___y_4493_: *mut leanh::LeanObject,
    mut v___y_4494_: *mut leanh::LeanObject,
    mut v___y_4495_: *mut leanh::LeanObject,
    mut v___y_4496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4497_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4485_, v_fst_4486_, v_fst_4487_, v_fst_4488_, v_fst_4489_, v_snd_4490_, v_x_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
    leanh::lean_dec(v___y_4495_);
    leanh::lean_dec_ref(v___y_4494_);
    leanh::lean_dec(v___y_4493_);
    leanh::lean_dec_ref(v___y_4492_);
    leanh::lean_dec_ref(v_x_4491_);
    return v_res_4497_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg(
    mut v_a_4500_: *mut leanh::LeanObject,
    mut v_b_4501_: *mut leanh::LeanObject,
    mut v___y_4502_: *mut leanh::LeanObject,
    mut v___y_4503_: *mut leanh::LeanObject,
    mut v___y_4504_: *mut leanh::LeanObject,
    mut v___y_4505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4512_: u8 = 0;
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4544_: u8 = 0;
    let mut v_a_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4551_: u8 = 0;
    let mut v_a_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut v___f_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: u8 = 0;
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: u8 = 0;
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: u8 = 0;
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: u8 = 0;
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: u8 = 0;
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: u8 = 0;
    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: u8 = 0;
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: u8 = 0;
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: u8 = 0;
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: u8 = 0;
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: u8 = 0;
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: u8 = 0;
    let mut v___x_4596_: u8 = 0;
    let mut v___x_4597_: u8 = 0;
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: u8 = 0;
    let mut v___x_4607_: u8 = 0;
    let mut v___x_4608_: u8 = 0;
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: u8 = 0;
    let mut v___x_4618_: u8 = 0;
    let mut v___x_4619_: u8 = 0;
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: u8 = 0;
    let mut v___x_4629_: u8 = 0;
    let mut v___x_4630_: u8 = 0;
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: u8 = 0;
    let mut v___x_4640_: u8 = 0;
    let mut v___x_4641_: u8 = 0;
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: u8 = 0;
    let mut v___x_4650_: u8 = 0;
    let mut v___x_4651_: u8 = 0;
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: u8 = 0;
    let mut v___x_4658_: u8 = 0;
    let mut v___x_4659_: u8 = 0;
    let mut v___x_4660_: u8 = 0;
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: u8 = 0;
    let mut v___x_4667_: u8 = 0;
    let mut v___x_4668_: u8 = 0;
    let mut v___x_4669_: u8 = 0;
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: u8 = 0;
    let mut v___x_4676_: u8 = 0;
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: u8 = 0;
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4705_: u8 = 0;
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4709_: u8 = 0;
    let mut v_a_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4713_: u8 = 0;
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4717_: u8 = 0;
    let mut v_a_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4721_: u8 = 0;
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4725_: u8 = 0;
    let mut v_a_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4729_: u8 = 0;
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4733_: u8 = 0;
    let mut v_isSharedCheck_4734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_4507_ = leanh::lean_ctor_get(v_a_4500_, 0);
                v_start_4508_ = leanh::lean_ctor_get(v_a_4500_, 1);
                v_stop_4509_ = leanh::lean_ctor_get(v_a_4500_, 2);
                v_isSharedCheck_4734_ = (!leanh::lean_is_exclusive(v_a_4500_)) as u8;
                if v_isSharedCheck_4734_ == 0 {
                    v___x_4511_ = v_a_4500_;
                    v_isShared_4512_ = v_isSharedCheck_4734_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_4509_);
                    leanh::lean_inc(v_start_4508_);
                    leanh::lean_inc(v_array_4507_);
                    leanh::lean_dec(v_a_4500_);
                    v___x_4511_ = leanh::lean_box(0);
                    v_isShared_4512_ = v_isSharedCheck_4734_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4513_ = lean_nat_dec_lt(v_start_4508_, v_stop_4509_);
                if v___x_4513_ == 0 {
                    leanh::lean_del_object(v___x_4511_);
                    leanh::lean_dec(v_stop_4509_);
                    leanh::lean_dec(v_start_4508_);
                    leanh::lean_dec_ref(v_array_4507_);
                    v___x_4514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4514_, 0, v_b_4501_);
                    return v___x_4514_;
                } else {
                    v___x_4515_ = lean_array_fget_borrowed(v_array_4507_, v_start_4508_);
                    v___x_4516_ = l_Lean_Expr_fvarId_x21(v___x_4515_);
                    v___x_4517_ = l_Lean_FVarId_getType___redArg(
                        v___x_4516_,
                        v___y_4502_,
                        v___y_4504_,
                        v___y_4505_,
                    );
                    if leanh::lean_obj_tag(v___x_4517_) == 0 {
                        v_a_4518_ = leanh::lean_ctor_get(v___x_4517_, 0);
                        leanh::lean_inc(v_a_4518_);
                        leanh::lean_dec_ref_known(v___x_4517_, 1);
                        v___x_4519_ = l_Lean_Compiler_LCNF_toLCNFType(
                            v_a_4518_,
                            v___y_4502_,
                            v___y_4503_,
                            v___y_4504_,
                            v___y_4505_,
                        );
                        if leanh::lean_obj_tag(v___x_4519_) == 0 {
                            v_a_4520_ = leanh::lean_ctor_get(v___x_4519_, 0);
                            leanh::lean_inc(v_a_4520_);
                            leanh::lean_dec_ref_known(v___x_4519_, 1);
                            v___x_4521_ = l_Lean_Compiler_LCNF_toMonoType(
                                v_a_4520_,
                                v___y_4504_,
                                v___y_4505_,
                            );
                            if leanh::lean_obj_tag(v___x_4521_) == 0 {
                                v_a_4522_ = leanh::lean_ctor_get(v___x_4521_, 0);
                                leanh::lean_inc(v_a_4522_);
                                leanh::lean_dec_ref_known(v___x_4521_, 1);
                                v___x_4523_ = l_Lean_Compiler_LCNF_toImpureType(
                                    v_a_4522_,
                                    v___y_4504_,
                                    v___y_4505_,
                                );
                                if leanh::lean_obj_tag(v___x_4523_) == 0 {
                                    v_snd_4524_ = leanh::lean_ctor_get(v_b_4501_, 1);
                                    leanh::lean_inc(v_snd_4524_);
                                    v_snd_4525_ = leanh::lean_ctor_get(v_snd_4524_, 1);
                                    leanh::lean_inc(v_snd_4525_);
                                    v_snd_4526_ = leanh::lean_ctor_get(v_snd_4525_, 1);
                                    leanh::lean_inc(v_snd_4526_);
                                    v_snd_4527_ = leanh::lean_ctor_get(v_snd_4526_, 1);
                                    leanh::lean_inc(v_snd_4527_);
                                    v_a_4528_ = leanh::lean_ctor_get(v___x_4523_, 0);
                                    leanh::lean_inc(v_a_4528_);
                                    leanh::lean_dec_ref_known(v___x_4523_, 1);
                                    v_fst_4529_ = leanh::lean_ctor_get(v_b_4501_, 0);
                                    leanh::lean_inc(v_fst_4529_);
                                    leanh::lean_dec_ref(v_b_4501_);
                                    v_fst_4530_ = leanh::lean_ctor_get(v_snd_4524_, 0);
                                    leanh::lean_inc(v_fst_4530_);
                                    leanh::lean_dec(v_snd_4524_);
                                    v_fst_4531_ = leanh::lean_ctor_get(v_snd_4525_, 0);
                                    leanh::lean_inc(v_fst_4531_);
                                    leanh::lean_dec(v_snd_4525_);
                                    v_fst_4532_ = leanh::lean_ctor_get(v_snd_4526_, 0);
                                    leanh::lean_inc(v_fst_4532_);
                                    leanh::lean_dec(v_snd_4526_);
                                    v_fst_4533_ = leanh::lean_ctor_get(v_snd_4527_, 0);
                                    leanh::lean_inc(v_fst_4533_);
                                    v_snd_4534_ = leanh::lean_ctor_get(v_snd_4527_, 1);
                                    leanh::lean_inc(v_snd_4534_);
                                    leanh::lean_dec(v_snd_4527_);
                                    v___x_4535_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_4536_ = lean_nat_add(v_start_4508_, v___x_4535_);
                                    leanh::lean_dec(v_start_4508_);
                                    if v_isShared_4512_ == 0 {
                                        leanh::lean_ctor_set(v___x_4511_, 1, v___x_4536_);
                                        v___x_4538_ = v___x_4511_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_4701_ =
                                            leanh::lean_alloc_ctor(0, 3, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4701_,
                                            0,
                                            v_array_4507_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4701_,
                                            1,
                                            v___x_4536_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_4701_,
                                            2,
                                            v_stop_4509_,
                                        );
                                        v___x_4538_ = v_reuseFailAlloc_4701_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_del_object(v___x_4511_);
                                    leanh::lean_dec(v_stop_4509_);
                                    leanh::lean_dec(v_start_4508_);
                                    leanh::lean_dec_ref(v_array_4507_);
                                    leanh::lean_dec_ref(v_b_4501_);
                                    v_a_4702_ = leanh::lean_ctor_get(v___x_4523_, 0);
                                    v_isSharedCheck_4709_ =
                                        (!leanh::lean_is_exclusive(v___x_4523_)) as u8;
                                    if v_isSharedCheck_4709_ == 0 {
                                        v___x_4704_ = v___x_4523_;
                                        v_isShared_4705_ = v_isSharedCheck_4709_;
                                        state = 8;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4702_);
                                        leanh::lean_dec(v___x_4523_);
                                        v___x_4704_ = leanh::lean_box(0);
                                        v_isShared_4705_ = v_isSharedCheck_4709_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_4511_);
                                leanh::lean_dec(v_stop_4509_);
                                leanh::lean_dec(v_start_4508_);
                                leanh::lean_dec_ref(v_array_4507_);
                                leanh::lean_dec_ref(v_b_4501_);
                                v_a_4710_ = leanh::lean_ctor_get(v___x_4521_, 0);
                                v_isSharedCheck_4717_ =
                                    (!leanh::lean_is_exclusive(v___x_4521_)) as u8;
                                if v_isSharedCheck_4717_ == 0 {
                                    v___x_4712_ = v___x_4521_;
                                    v_isShared_4713_ = v_isSharedCheck_4717_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4710_);
                                    leanh::lean_dec(v___x_4521_);
                                    v___x_4712_ = leanh::lean_box(0);
                                    v_isShared_4713_ = v_isSharedCheck_4717_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_4511_);
                            leanh::lean_dec(v_stop_4509_);
                            leanh::lean_dec(v_start_4508_);
                            leanh::lean_dec_ref(v_array_4507_);
                            leanh::lean_dec_ref(v_b_4501_);
                            v_a_4718_ = leanh::lean_ctor_get(v___x_4519_, 0);
                            v_isSharedCheck_4725_ =
                                (!leanh::lean_is_exclusive(v___x_4519_)) as u8;
                            if v_isSharedCheck_4725_ == 0 {
                                v___x_4720_ = v___x_4519_;
                                v_isShared_4721_ = v_isSharedCheck_4725_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4718_);
                                leanh::lean_dec(v___x_4519_);
                                v___x_4720_ = leanh::lean_box(0);
                                v_isShared_4721_ = v_isSharedCheck_4725_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_4511_);
                        leanh::lean_dec(v_stop_4509_);
                        leanh::lean_dec(v_start_4508_);
                        leanh::lean_dec_ref(v_array_4507_);
                        leanh::lean_dec_ref(v_b_4501_);
                        v_a_4726_ = leanh::lean_ctor_get(v___x_4517_, 0);
                        v_isSharedCheck_4733_ =
                            (!leanh::lean_is_exclusive(v___x_4517_)) as u8;
                        if v_isSharedCheck_4733_ == 0 {
                            v___x_4728_ = v___x_4517_;
                            v_isShared_4729_ = v_isSharedCheck_4733_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4726_);
                            leanh::lean_dec(v___x_4517_);
                            v___x_4728_ = leanh::lean_box(0);
                            v_isShared_4729_ = v_isSharedCheck_4733_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_fst_4529_);
                v___f_4560_ = leanh::lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 1);
                leanh::lean_closure_set(v___f_4560_, 0, v_fst_4529_);
                if leanh::lean_obj_tag(v_a_4528_) == 4 {
                    v_declName_4561_ = leanh::lean_ctor_get(v_a_4528_, 0);
                    if leanh::lean_obj_tag(v_declName_4561_) == 1 {
                        v_pre_4562_ = leanh::lean_ctor_get(v_declName_4561_, 0);
                        if leanh::lean_obj_tag(v_pre_4562_) == 0 {
                            v_us_4563_ = leanh::lean_ctor_get(v_a_4528_, 1);
                            v_str_4564_ = leanh::lean_ctor_get(v_declName_4561_, 1);
                            v___x_4565_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__3;
                            v___x_4566_ = lean_string_dec_eq(v_str_4564_, v___x_4565_);
                            if v___x_4566_ == 0 {
                                v___x_4567_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__0;
                                v___x_4568_ = lean_string_dec_eq(v_str_4564_, v___x_4567_);
                                if v___x_4568_ == 0 {
                                    v___x_4569_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__0;
                                    v___x_4570_ = lean_string_dec_eq(v_str_4564_, v___x_4569_);
                                    if v___x_4570_ == 0 {
                                        v___x_4571_ = leanh::lean_unsigned_to_nat(0);
                                        v___x_4572_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__7;
                                        v___x_4573_ = lean_string_dec_eq(v_str_4564_, v___x_4572_);
                                        if v___x_4573_ == 0 {
                                            v___x_4574_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__10;
                                            v___x_4575_ =
                                                lean_string_dec_eq(v_str_4564_, v___x_4574_);
                                            if v___x_4575_ == 0 {
                                                v___x_4576_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__12;
                                                v___x_4577_ =
                                                    lean_string_dec_eq(v_str_4564_, v___x_4576_);
                                                if v___x_4577_ == 0 {
                                                    v___x_4578_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__9;
                                                    v___x_4579_ = lean_string_dec_eq(
                                                        v_str_4564_,
                                                        v___x_4578_,
                                                    );
                                                    if v___x_4579_ == 0 {
                                                        v___x_4580_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__6;
                                                        v___x_4581_ = lean_string_dec_eq(
                                                            v_str_4564_,
                                                            v___x_4580_,
                                                        );
                                                        if v___x_4581_ == 0 {
                                                            v___x_4582_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__3;
                                                            v___x_4583_ = lean_string_dec_eq(
                                                                v_str_4564_,
                                                                v___x_4582_,
                                                            );
                                                            if v___x_4583_ == 0 {
                                                                v___x_4584_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__6;
                                                                v___x_4585_ = lean_string_dec_eq(
                                                                    v_str_4564_,
                                                                    v___x_4584_,
                                                                );
                                                                if v___x_4585_ == 0 {
                                                                    v___x_4586_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__9;
                                                                    v___x_4587_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_4564_,
                                                                            v___x_4586_,
                                                                        );
                                                                    if v___x_4587_ == 0 {
                                                                        v___x_4588_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__8;
                                                                        v___x_4589_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_4564_,
                                                                                v___x_4588_,
                                                                            );
                                                                        if v___x_4589_ == 0 {
                                                                            leanh::lean_dec(
                                                                                v_fst_4529_,
                                                                            );
                                                                            v___x_4590_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v_a_4528_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                                            leanh::lean_dec_ref_known(v_a_4528_, 2);
                                                                            v___y_4540_ =
                                                                                v___x_4590_;
                                                                            state = 3;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_pre_4562_,
                                                                            );
                                                                            leanh::lean_inc(
                                                                                v_us_4563_,
                                                                            );
                                                                            leanh::lean_dec_ref_known(v_a_4528_, 2);
                                                                            if leanh::lean_obj_tag(v_us_4563_) == 0 {
leanh::lean_dec_ref(v___f_4560_);
leanh::lean_dec(v_snd_4534_);
v___x_4591_ = leanh::lean_unsigned_to_nat(8);
v___x_4592_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__19;
v___x_4593_ = l_Lean_Expr_const___override(v___x_4592_, v_us_4563_);
v___x_4594_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
leanh::lean_ctor_set(v___x_4594_, 0, v___x_4591_);
leanh::lean_ctor_set(v___x_4594_, 1, v___x_4571_);
leanh::lean_ctor_set(v___x_4594_, 2, v___x_4593_);
v___x_4595_ = (leanh::lean_unbox(v_fst_4531_) as u8);
leanh::lean_dec(v_fst_4531_);
v___x_4596_ = (leanh::lean_unbox(v_fst_4532_) as u8);
leanh::lean_dec(v_fst_4532_);
v___x_4597_ = (leanh::lean_unbox(v_fst_4533_) as u8);
leanh::lean_dec(v_fst_4533_);
v___x_4598_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_4529_, v___x_4594_, v_fst_4530_, v___x_4595_, v___x_4596_, v___x_4597_, v___x_4589_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
v___y_4540_ = v___x_4598_;
state = 3; continue;
} else {
leanh::lean_dec(v_fst_4529_);
v___x_4599_ = l_Lean_Name_str___override(v_pre_4562_, v___x_4588_);
v___x_4600_ = l_Lean_Expr_const___override(v___x_4599_, v_us_4563_);
v___x_4601_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4600_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
leanh::lean_dec_ref(v___x_4600_);
v___y_4540_ = v___x_4601_;
state = 3; continue;
}
                                                                        }
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_pre_4562_,
                                                                        );
                                                                        leanh::lean_inc(
                                                                            v_us_4563_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v_a_4528_, 2);
                                                                        if leanh::lean_obj_tag(v_us_4563_) == 0 {
leanh::lean_dec_ref(v___f_4560_);
leanh::lean_dec(v_fst_4533_);
v___x_4602_ = leanh::lean_unsigned_to_nat(4);
v___x_4603_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__17;
v___x_4604_ = l_Lean_Expr_const___override(v___x_4603_, v_us_4563_);
v___x_4605_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
leanh::lean_ctor_set(v___x_4605_, 0, v___x_4602_);
leanh::lean_ctor_set(v___x_4605_, 1, v___x_4571_);
leanh::lean_ctor_set(v___x_4605_, 2, v___x_4604_);
v___x_4606_ = (leanh::lean_unbox(v_fst_4531_) as u8);
leanh::lean_dec(v_fst_4531_);
v___x_4607_ = (leanh::lean_unbox(v_fst_4532_) as u8);
leanh::lean_dec(v_fst_4532_);
v___x_4608_ = (leanh::lean_unbox(v_snd_4534_) as u8);
leanh::lean_dec(v_snd_4534_);
v___x_4609_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_4529_, v___x_4605_, v_fst_4530_, v___x_4606_, v___x_4607_, v___x_4587_, v___x_4608_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
v___y_4540_ = v___x_4609_;
state = 3; continue;
} else {
leanh::lean_dec(v_fst_4529_);
v___x_4610_ = l_Lean_Name_str___override(v_pre_4562_, v___x_4586_);
v___x_4611_ = l_Lean_Expr_const___override(v___x_4610_, v_us_4563_);
v___x_4612_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4611_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
leanh::lean_dec_ref(v___x_4611_);
v___y_4540_ = v___x_4612_;
state = 3; continue;
}
                                                                    }
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_pre_4562_,
                                                                    );
                                                                    leanh::lean_inc(
                                                                        v_us_4563_,
                                                                    );
                                                                    leanh::lean_dec_ref_known(v_a_4528_, 2);
                                                                    if leanh::lean_obj_tag(
                                                                        v_us_4563_,
                                                                    ) == 0
                                                                    {
                                                                        leanh::lean_dec_ref(
                                                                            v___f_4560_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_snd_4534_,
                                                                        );
                                                                        v___x_4613_ = leanh::lean_unsigned_to_nat(8);
                                                                        v___x_4614_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache___closed__23;
                                                                        v___x_4615_ = l_Lean_Expr_const___override(v___x_4614_, v_us_4563_);
                                                                        v___x_4616_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
                                                                        leanh::lean_ctor_set(
                                                                            v___x_4616_,
                                                                            0,
                                                                            v___x_4613_,
                                                                        );
                                                                        leanh::lean_ctor_set(
                                                                            v___x_4616_,
                                                                            1,
                                                                            v___x_4571_,
                                                                        );
                                                                        leanh::lean_ctor_set(
                                                                            v___x_4616_,
                                                                            2,
                                                                            v___x_4615_,
                                                                        );
                                                                        v___x_4617_ = (leanh::lean_unbox(v_fst_4531_) as u8);
                                                                        leanh::lean_dec(
                                                                            v_fst_4531_,
                                                                        );
                                                                        v___x_4618_ = (leanh::lean_unbox(v_fst_4532_) as u8);
                                                                        leanh::lean_dec(
                                                                            v_fst_4532_,
                                                                        );
                                                                        v___x_4619_ = (leanh::lean_unbox(v_fst_4533_) as u8);
                                                                        leanh::lean_dec(
                                                                            v_fst_4533_,
                                                                        );
                                                                        v___x_4620_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_4529_, v___x_4616_, v_fst_4530_, v___x_4617_, v___x_4618_, v___x_4619_, v___x_4585_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                                        v___y_4540_ = v___x_4620_;
                                                                        state = 3;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_dec(
                                                                            v_fst_4529_,
                                                                        );
                                                                        v___x_4621_ = l_Lean_Name_str___override(v_pre_4562_, v___x_4584_);
                                                                        v___x_4622_ = l_Lean_Expr_const___override(v___x_4621_, v_us_4563_);
                                                                        v___x_4623_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4622_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                                        leanh::lean_dec_ref(
                                                                            v___x_4622_,
                                                                        );
                                                                        v___y_4540_ = v___x_4623_;
                                                                        state = 3;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_inc(v_pre_4562_);
                                                                leanh::lean_inc(v_us_4563_);
                                                                leanh::lean_dec_ref_known(
                                                                    v_a_4528_, 2,
                                                                );
                                                                if leanh::lean_obj_tag(
                                                                    v_us_4563_,
                                                                ) == 0
                                                                {
                                                                    leanh::lean_dec_ref(
                                                                        v___f_4560_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_fst_4533_,
                                                                    );
                                                                    v___x_4624_ = leanh::lean_unsigned_to_nat(4);
                                                                    v___x_4625_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__4;
                                                                    v___x_4626_ = l_Lean_Expr_const___override(v___x_4625_, v_us_4563_);
                                                                    v___x_4627_ = leanh::lean_alloc_ctor(3, 3, (0) as u32);
                                                                    leanh::lean_ctor_set(
                                                                        v___x_4627_,
                                                                        0,
                                                                        v___x_4624_,
                                                                    );
                                                                    leanh::lean_ctor_set(
                                                                        v___x_4627_,
                                                                        1,
                                                                        v___x_4571_,
                                                                    );
                                                                    leanh::lean_ctor_set(
                                                                        v___x_4627_,
                                                                        2,
                                                                        v___x_4626_,
                                                                    );
                                                                    v___x_4628_ =
                                                                        (leanh::lean_unbox(
                                                                            v_fst_4531_,
                                                                        )
                                                                            as u8);
                                                                    leanh::lean_dec(
                                                                        v_fst_4531_,
                                                                    );
                                                                    v___x_4629_ =
                                                                        (leanh::lean_unbox(
                                                                            v_fst_4532_,
                                                                        )
                                                                            as u8);
                                                                    leanh::lean_dec(
                                                                        v_fst_4532_,
                                                                    );
                                                                    v___x_4630_ =
                                                                        (leanh::lean_unbox(
                                                                            v_snd_4534_,
                                                                        )
                                                                            as u8);
                                                                    leanh::lean_dec(
                                                                        v_snd_4534_,
                                                                    );
                                                                    v___x_4631_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_4529_, v___x_4627_, v_fst_4530_, v___x_4628_, v___x_4629_, v___x_4583_, v___x_4630_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                                    v___y_4540_ = v___x_4631_;
                                                                    state = 3;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v_fst_4529_,
                                                                    );
                                                                    v___x_4632_ =
                                                                        l_Lean_Name_str___override(
                                                                            v_pre_4562_,
                                                                            v___x_4582_,
                                                                        );
                                                                    v___x_4633_ = l_Lean_Expr_const___override(v___x_4632_, v_us_4563_);
                                                                    v___x_4634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4633_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                                    leanh::lean_dec_ref(
                                                                        v___x_4633_,
                                                                    );
                                                                    v___y_4540_ = v___x_4634_;
                                                                    state = 3;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            leanh::lean_inc(v_pre_4562_);
                                                            leanh::lean_inc(v_us_4563_);
                                                            leanh::lean_dec_ref_known(
                                                                v_a_4528_, 2,
                                                            );
                                                            if leanh::lean_obj_tag(
                                                                v_us_4563_,
                                                            ) == 0
                                                            {
                                                                leanh::lean_dec_ref(
                                                                    v___f_4560_,
                                                                );
                                                                leanh::lean_dec(v_fst_4532_);
                                                                v___x_4635_ = leanh::lean_unsigned_to_nat(2);
                                                                v___x_4636_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__7;
                                                                v___x_4637_ =
                                                                    l_Lean_Expr_const___override(
                                                                        v___x_4636_,
                                                                        v_us_4563_,
                                                                    );
                                                                v___x_4638_ =
                                                                    leanh::lean_alloc_ctor(
                                                                        3,
                                                                        3,
                                                                        (0) as u32,
                                                                    );
                                                                leanh::lean_ctor_set(
                                                                    v___x_4638_,
                                                                    0,
                                                                    v___x_4635_,
                                                                );
                                                                leanh::lean_ctor_set(
                                                                    v___x_4638_,
                                                                    1,
                                                                    v___x_4571_,
                                                                );
                                                                leanh::lean_ctor_set(
                                                                    v___x_4638_,
                                                                    2,
                                                                    v___x_4637_,
                                                                );
                                                                v___x_4639_ =
                                                                    (leanh::lean_unbox(
                                                                        v_fst_4531_,
                                                                    )
                                                                        as u8);
                                                                leanh::lean_dec(v_fst_4531_);
                                                                v___x_4640_ =
                                                                    (leanh::lean_unbox(
                                                                        v_fst_4533_,
                                                                    )
                                                                        as u8);
                                                                leanh::lean_dec(v_fst_4533_);
                                                                v___x_4641_ =
                                                                    (leanh::lean_unbox(
                                                                        v_snd_4534_,
                                                                    )
                                                                        as u8);
                                                                leanh::lean_dec(v_snd_4534_);
                                                                v___x_4642_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_4529_, v___x_4638_, v_fst_4530_, v___x_4639_, v___x_4581_, v___x_4640_, v___x_4641_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                                v___y_4540_ = v___x_4642_;
                                                                state = 3;
                                                                continue;
                                                            } else {
                                                                leanh::lean_dec(v_fst_4529_);
                                                                v___x_4643_ =
                                                                    l_Lean_Name_str___override(
                                                                        v_pre_4562_,
                                                                        v___x_4580_,
                                                                    );
                                                                v___x_4644_ =
                                                                    l_Lean_Expr_const___override(
                                                                        v___x_4643_,
                                                                        v_us_4563_,
                                                                    );
                                                                v___x_4645_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4644_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                                leanh::lean_dec_ref(
                                                                    v___x_4644_,
                                                                );
                                                                v___y_4540_ = v___x_4645_;
                                                                state = 3;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_inc(v_pre_4562_);
                                                        leanh::lean_inc(v_us_4563_);
                                                        leanh::lean_dec_ref_known(
                                                            v_a_4528_, 2,
                                                        );
                                                        if leanh::lean_obj_tag(v_us_4563_)
                                                            == 0
                                                        {
                                                            leanh::lean_dec_ref(v___f_4560_);
                                                            leanh::lean_dec(v_fst_4531_);
                                                            v___x_4646_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeForEnum___closed__10;
                                                            v___x_4647_ =
                                                                l_Lean_Expr_const___override(
                                                                    v___x_4646_,
                                                                    v_us_4563_,
                                                                );
                                                            v___x_4648_ =
                                                                leanh::lean_alloc_ctor(
                                                                    3,
                                                                    3,
                                                                    (0) as u32,
                                                                );
                                                            leanh::lean_ctor_set(
                                                                v___x_4648_,
                                                                0,
                                                                v___x_4535_,
                                                            );
                                                            leanh::lean_ctor_set(
                                                                v___x_4648_,
                                                                1,
                                                                v___x_4571_,
                                                            );
                                                            leanh::lean_ctor_set(
                                                                v___x_4648_,
                                                                2,
                                                                v___x_4647_,
                                                            );
                                                            v___x_4649_ = (leanh::lean_unbox(
                                                                v_fst_4532_,
                                                            )
                                                                as u8);
                                                            leanh::lean_dec(v_fst_4532_);
                                                            v___x_4650_ = (leanh::lean_unbox(
                                                                v_fst_4533_,
                                                            )
                                                                as u8);
                                                            leanh::lean_dec(v_fst_4533_);
                                                            v___x_4651_ = (leanh::lean_unbox(
                                                                v_snd_4534_,
                                                            )
                                                                as u8);
                                                            leanh::lean_dec(v_snd_4534_);
                                                            v___x_4652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_4529_, v___x_4648_, v_fst_4530_, v___x_4579_, v___x_4649_, v___x_4650_, v___x_4651_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                            v___y_4540_ = v___x_4652_;
                                                            state = 3;
                                                            continue;
                                                        } else {
                                                            leanh::lean_dec(v_fst_4529_);
                                                            v___x_4653_ =
                                                                l_Lean_Name_str___override(
                                                                    v_pre_4562_,
                                                                    v___x_4578_,
                                                                );
                                                            v___x_4654_ =
                                                                l_Lean_Expr_const___override(
                                                                    v___x_4653_,
                                                                    v_us_4563_,
                                                                );
                                                            v___x_4655_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4654_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                            leanh::lean_dec_ref(v___x_4654_);
                                                            v___y_4540_ = v___x_4655_;
                                                            state = 3;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_inc(v_pre_4562_);
                                                    leanh::lean_inc(v_us_4563_);
                                                    leanh::lean_dec_ref_known(v_a_4528_, 2);
                                                    if leanh::lean_obj_tag(v_us_4563_) == 0 {
                                                        leanh::lean_dec_ref(v___f_4560_);
                                                        v___x_4656_ = leanh::lean_box(4);
                                                        v___x_4657_ =
                                                            (leanh::lean_unbox(v_fst_4531_)
                                                                as u8);
                                                        leanh::lean_dec(v_fst_4531_);
                                                        v___x_4658_ =
                                                            (leanh::lean_unbox(v_fst_4532_)
                                                                as u8);
                                                        leanh::lean_dec(v_fst_4532_);
                                                        v___x_4659_ =
                                                            (leanh::lean_unbox(v_fst_4533_)
                                                                as u8);
                                                        leanh::lean_dec(v_fst_4533_);
                                                        v___x_4660_ =
                                                            (leanh::lean_unbox(v_snd_4534_)
                                                                as u8);
                                                        leanh::lean_dec(v_snd_4534_);
                                                        v___x_4661_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_4529_, v___x_4656_, v_fst_4530_, v___x_4657_, v___x_4658_, v___x_4659_, v___x_4660_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                        v___y_4540_ = v___x_4661_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        leanh::lean_dec(v_fst_4529_);
                                                        v___x_4662_ = l_Lean_Name_str___override(
                                                            v_pre_4562_,
                                                            v___x_4576_,
                                                        );
                                                        v___x_4663_ = l_Lean_Expr_const___override(
                                                            v___x_4662_,
                                                            v_us_4563_,
                                                        );
                                                        v___x_4664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4663_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                        leanh::lean_dec_ref(v___x_4663_);
                                                        v___y_4540_ = v___x_4664_;
                                                        state = 3;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                leanh::lean_inc(v_pre_4562_);
                                                leanh::lean_inc(v_us_4563_);
                                                leanh::lean_dec_ref_known(v_a_4528_, 2);
                                                if leanh::lean_obj_tag(v_us_4563_) == 0 {
                                                    leanh::lean_dec_ref(v___f_4560_);
                                                    v___x_4665_ = leanh::lean_box(0);
                                                    v___x_4666_ =
                                                        (leanh::lean_unbox(v_fst_4531_)
                                                            as u8);
                                                    leanh::lean_dec(v_fst_4531_);
                                                    v___x_4667_ =
                                                        (leanh::lean_unbox(v_fst_4532_)
                                                            as u8);
                                                    leanh::lean_dec(v_fst_4532_);
                                                    v___x_4668_ =
                                                        (leanh::lean_unbox(v_fst_4533_)
                                                            as u8);
                                                    leanh::lean_dec(v_fst_4533_);
                                                    v___x_4669_ =
                                                        (leanh::lean_unbox(v_snd_4534_)
                                                            as u8);
                                                    leanh::lean_dec(v_snd_4534_);
                                                    v___x_4670_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_4529_, v___x_4665_, v_fst_4530_, v___x_4666_, v___x_4667_, v___x_4668_, v___x_4669_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                    v___y_4540_ = v___x_4670_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    leanh::lean_dec(v_fst_4529_);
                                                    v___x_4671_ = l_Lean_Name_str___override(
                                                        v_pre_4562_,
                                                        v___x_4574_,
                                                    );
                                                    v___x_4672_ = l_Lean_Expr_const___override(
                                                        v___x_4671_,
                                                        v_us_4563_,
                                                    );
                                                    v___x_4673_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4672_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                    leanh::lean_dec_ref(v___x_4672_);
                                                    v___y_4540_ = v___x_4673_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_inc(v_pre_4562_);
                                            leanh::lean_inc(v_us_4563_);
                                            leanh::lean_dec_ref_known(v_a_4528_, 2);
                                            if leanh::lean_obj_tag(v_us_4563_) == 0 {
                                                leanh::lean_dec_ref(v___f_4560_);
                                                v___x_4674_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___closed__0;
                                                v___x_4675_ =
                                                    (leanh::lean_unbox(v_fst_4531_) as u8);
                                                leanh::lean_dec(v_fst_4531_);
                                                v___x_4676_ =
                                                    (leanh::lean_unbox(v_fst_4532_) as u8);
                                                leanh::lean_dec(v_fst_4532_);
                                                v___x_4677_ =
                                                    (leanh::lean_unbox(v_fst_4533_) as u8);
                                                leanh::lean_dec(v_fst_4533_);
                                                v___x_4678_ =
                                                    (leanh::lean_unbox(v_snd_4534_) as u8);
                                                leanh::lean_dec(v_snd_4534_);
                                                v___x_4679_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__0(v_fst_4529_, v___x_4674_, v_fst_4530_, v___x_4675_, v___x_4676_, v___x_4677_, v___x_4678_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                v___y_4540_ = v___x_4679_;
                                                state = 3;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_fst_4529_);
                                                v___x_4680_ = l_Lean_Name_str___override(
                                                    v_pre_4562_,
                                                    v___x_4572_,
                                                );
                                                v___x_4681_ = l_Lean_Expr_const___override(
                                                    v___x_4680_,
                                                    v_us_4563_,
                                                );
                                                v___x_4682_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4681_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                                leanh::lean_dec_ref(v___x_4681_);
                                                v___y_4540_ = v___x_4682_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_fst_4529_);
                                        if leanh::lean_obj_tag(v_us_4563_) == 0 {
                                            v___x_4683_ = leanh::lean_box(0);
                                            v___x_4684_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_4530_, v___x_4535_, v_a_4528_, v___f_4560_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4683_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                            v___y_4540_ = v___x_4684_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_pre_4562_);
                                            leanh::lean_inc(v_us_4563_);
                                            leanh::lean_dec_ref_known(v_a_4528_, 2);
                                            v___x_4685_ = l_Lean_Name_str___override(
                                                v_pre_4562_,
                                                v___x_4569_,
                                            );
                                            v___x_4686_ = l_Lean_Expr_const___override(
                                                v___x_4685_,
                                                v_us_4563_,
                                            );
                                            v___x_4687_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4686_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                            leanh::lean_dec_ref(v___x_4686_);
                                            v___y_4540_ = v___x_4687_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_fst_4529_);
                                    if leanh::lean_obj_tag(v_us_4563_) == 0 {
                                        v___x_4688_ = leanh::lean_box(0);
                                        v___x_4689_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_4530_, v___x_4535_, v_a_4528_, v___f_4560_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4688_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                        v___y_4540_ = v___x_4689_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_pre_4562_);
                                        leanh::lean_inc(v_us_4563_);
                                        leanh::lean_dec_ref_known(v_a_4528_, 2);
                                        v___x_4690_ =
                                            l_Lean_Name_str___override(v_pre_4562_, v___x_4567_);
                                        v___x_4691_ =
                                            l_Lean_Expr_const___override(v___x_4690_, v_us_4563_);
                                        v___x_4692_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4691_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                        leanh::lean_dec_ref(v___x_4691_);
                                        v___y_4540_ = v___x_4692_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_fst_4529_);
                                if leanh::lean_obj_tag(v_us_4563_) == 0 {
                                    v___x_4693_ = leanh::lean_box(0);
                                    v___x_4694_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__2(v_fst_4530_, v___x_4535_, v_a_4528_, v___f_4560_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4693_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                    v___y_4540_ = v___x_4694_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_pre_4562_);
                                    leanh::lean_inc(v_us_4563_);
                                    leanh::lean_dec_ref_known(v_a_4528_, 2);
                                    v___x_4695_ =
                                        l_Lean_Name_str___override(v_pre_4562_, v___x_4565_);
                                    v___x_4696_ =
                                        l_Lean_Expr_const___override(v___x_4695_, v_us_4563_);
                                    v___x_4697_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v___x_4696_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                                    leanh::lean_dec_ref(v___x_4696_);
                                    v___y_4540_ = v___x_4697_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_fst_4529_);
                            v___x_4698_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v_a_4528_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                            leanh::lean_dec_ref_known(v_a_4528_, 2);
                            v___y_4540_ = v___x_4698_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_fst_4529_);
                        v___x_4699_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v_a_4528_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                        leanh::lean_dec_ref_known(v_a_4528_, 2);
                        v___y_4540_ = v___x_4699_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_4529_);
                    v___x_4700_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1(v___f_4560_, v_fst_4530_, v_fst_4531_, v_fst_4532_, v_fst_4533_, v_snd_4534_, v_a_4528_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
                    leanh::lean_dec(v_a_4528_);
                    v___y_4540_ = v___x_4700_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v___y_4540_) == 0 {
                    v_a_4541_ = leanh::lean_ctor_get(v___y_4540_, 0);
                    v_isSharedCheck_4551_ = (!leanh::lean_is_exclusive(v___y_4540_)) as u8;
                    if v_isSharedCheck_4551_ == 0 {
                        v___x_4543_ = v___y_4540_;
                        v_isShared_4544_ = v_isSharedCheck_4551_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4541_);
                        leanh::lean_dec(v___y_4540_);
                        v___x_4543_ = leanh::lean_box(0);
                        v_isShared_4544_ = v_isSharedCheck_4551_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4538_);
                    v_a_4552_ = leanh::lean_ctor_get(v___y_4540_, 0);
                    v_isSharedCheck_4559_ = (!leanh::lean_is_exclusive(v___y_4540_)) as u8;
                    if v_isSharedCheck_4559_ == 0 {
                        v___x_4554_ = v___y_4540_;
                        v_isShared_4555_ = v_isSharedCheck_4559_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4552_);
                        leanh::lean_dec(v___y_4540_);
                        v___x_4554_ = leanh::lean_box(0);
                        v_isShared_4555_ = v_isSharedCheck_4559_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if leanh::lean_obj_tag(v_a_4541_) == 0 {
                    leanh::lean_dec_ref(v___x_4538_);
                    v_a_4545_ = leanh::lean_ctor_get(v_a_4541_, 0);
                    leanh::lean_inc(v_a_4545_);
                    leanh::lean_dec_ref_known(v_a_4541_, 1);
                    if v_isShared_4544_ == 0 {
                        leanh::lean_ctor_set(v___x_4543_, 0, v_a_4545_);
                        v___x_4547_ = v___x_4543_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4548_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4545_);
                        v___x_4547_ = v_reuseFailAlloc_4548_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4543_);
                    v_a_4549_ = leanh::lean_ctor_get(v_a_4541_, 0);
                    leanh::lean_inc(v_a_4549_);
                    leanh::lean_dec_ref_known(v_a_4541_, 1);
                    v_a_4500_ = v___x_4538_;
                    v_b_4501_ = v_a_4549_;
                    state = 0;
                    continue;
                }
            }
            5 => {
                return v___x_4547_;
            }
            6 => {
                if v_isShared_4555_ == 0 {
                    v___x_4557_ = v___x_4554_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
                    v___x_4557_ = v_reuseFailAlloc_4558_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4557_;
            }
            8 => {
                if v_isShared_4705_ == 0 {
                    v___x_4707_ = v___x_4704_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4708_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
                    v___x_4707_ = v_reuseFailAlloc_4708_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4707_;
            }
            10 => {
                if v_isShared_4713_ == 0 {
                    v___x_4715_ = v___x_4712_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
                    v___x_4715_ = v_reuseFailAlloc_4716_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4715_;
            }
            12 => {
                if v_isShared_4721_ == 0 {
                    v___x_4723_ = v___x_4720_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4724_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
                    v___x_4723_ = v_reuseFailAlloc_4724_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4723_;
            }
            14 => {
                if v_isShared_4729_ == 0 {
                    v___x_4731_ = v___x_4728_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4732_, 0, v_a_4726_);
                    v___x_4731_ = v_reuseFailAlloc_4732_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___boxed(
    mut v_a_4735_: *mut leanh::LeanObject,
    mut v_b_4736_: *mut leanh::LeanObject,
    mut v___y_4737_: *mut leanh::LeanObject,
    mut v___y_4738_: *mut leanh::LeanObject,
    mut v___y_4739_: *mut leanh::LeanObject,
    mut v___y_4740_: *mut leanh::LeanObject,
    mut v___y_4741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4742_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg(v_a_4735_, v_b_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_);
    leanh::lean_dec(v___y_4740_);
    leanh::lean_dec_ref(v___y_4739_);
    leanh::lean_dec(v___y_4738_);
    leanh::lean_dec_ref(v___y_4737_);
    return v_res_4742_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__4(
    mut v_sz_4743_: usize,
    mut v_i_4744_: usize,
    mut v_bs_4745_: *mut leanh::LeanObject,
    mut v___y_4746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4747_: u8 = 0;
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: usize = 0;
    let mut v___x_4756_: usize = 0;
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4767_: u8 = 0;
    let mut v_unused_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4747_ = lean_usize_dec_lt(v_i_4744_, v_sz_4743_);
                if v___x_4747_ == 0 {
                    v___x_4748_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4748_, 0, v_bs_4745_);
                    leanh::lean_ctor_set(v___x_4748_, 1, v___y_4746_);
                    return v___x_4748_;
                } else {
                    v_v_4749_ = lean_array_uget(v_bs_4745_, v_i_4744_);
                    v___x_4750_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4751_ = lean_array_uset(v_bs_4745_, v_i_4744_, v___x_4750_);
                    match leanh::lean_obj_tag(v_v_4749_) {
                        1 => {
                            v_fst_4753_ = v_v_4749_;
                            v_snd_4754_ = v___y_4746_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_isSharedCheck_4767_ =
                                (!leanh::lean_is_exclusive(v_v_4749_)) as u8;
                            if v_isSharedCheck_4767_ == 0 {
                                v_unused_4768_ = leanh::lean_ctor_get(v_v_4749_, 0);
                                leanh::lean_dec(v_unused_4768_);
                                v___x_4760_ = v_v_4749_;
                                v_isShared_4761_ = v_isSharedCheck_4767_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_v_4749_);
                                v___x_4760_ = leanh::lean_box(0);
                                v_isShared_4761_ = v_isSharedCheck_4767_;
                                state = 2;
                                continue;
                            }
                        }
                        3 => {
                            v_fst_4753_ = v_v_4749_;
                            v_snd_4754_ = v___y_4746_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_fst_4753_ = v_v_4749_;
                            v_snd_4754_ = v___y_4746_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4755_ = 1usize;
                v___x_4756_ = lean_usize_add(v_i_4744_, v___x_4755_);
                v___x_4757_ = lean_array_uset(v_bs_x27_4751_, v_i_4744_, v_fst_4753_);
                v_i_4744_ = v___x_4756_;
                v_bs_4745_ = v___x_4757_;
                v___y_4746_ = v_snd_4754_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4762_ = leanh::lean_unsigned_to_nat(1);
                v___x_4763_ = lean_nat_add(v___y_4746_, v___x_4762_);
                if v_isShared_4761_ == 0 {
                    leanh::lean_ctor_set(v___x_4760_, 0, v___y_4746_);
                    v___x_4765_ = v___x_4760_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4766_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4766_, 0, v___y_4746_);
                    v___x_4765_ = v_reuseFailAlloc_4766_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_4753_ = v___x_4765_;
                v_snd_4754_ = v___x_4763_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__4___boxed(
    mut v_sz_4769_: *mut leanh::LeanObject,
    mut v_i_4770_: *mut leanh::LeanObject,
    mut v_bs_4771_: *mut leanh::LeanObject,
    mut v___y_4772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4773_: usize = 0;
    let mut v_i_boxed_4774_: usize = 0;
    let mut v_res_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4773_ = leanh::lean_unbox_usize(v_sz_4769_);
    leanh::lean_dec(v_sz_4769_);
    v_i_boxed_4774_ = leanh::lean_unbox_usize(v_i_4770_);
    leanh::lean_dec(v_i_4770_);
    v_res_4775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__4(v_sz_boxed_4773_, v_i_boxed_4774_, v_bs_4771_, v___y_4772_);
    return v_res_4775_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___lam__1(
    mut v_numFields_4776_: *mut leanh::LeanObject,
    mut v_numParams_4777_: *mut leanh::LeanObject,
    mut v___x_4778_: u8,
    mut v_ctorName_4779_: *mut leanh::LeanObject,
    mut v_cidx_4780_: *mut leanh::LeanObject,
    mut v___f_4781_: *mut leanh::LeanObject,
    mut v_params_4782_: *mut leanh::LeanObject,
    mut v_x_4783_: *mut leanh::LeanObject,
    mut v___y_4784_: *mut leanh::LeanObject,
    mut v___y_4785_: *mut leanh::LeanObject,
    mut v___y_4786_: *mut leanh::LeanObject,
    mut v___y_4787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4806_: u8 = 0;
    let mut v_snd_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4811_: usize = 0;
    let mut v___x_4812_: usize = 0;
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4824_: u8 = 0;
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextOffset_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextOffset_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: u8 = 0;
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextOffset_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: u8 = 0;
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fields_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextOffset_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: u8 = 0;
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: u8 = 0;
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4865_: u8 = 0;
    let mut v_isSharedCheck_4866_: u8 = 0;
    let mut v_a_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4870_: u8 = 0;
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4789_ = lean_mk_empty_array_with_capacity(v_numFields_4776_);
                v___x_4790_ = leanh::lean_unsigned_to_nat(0);
                v___x_4791_ = lean_nat_add(v_numParams_4777_, v_numFields_4776_);
                v___x_4792_ =
                    l_Array_toSubarray___redArg(v_params_4782_, v_numParams_4777_, v___x_4791_);
                v___x_4793_ = leanh::lean_box((v___x_4778_) as usize);
                v___x_4794_ = leanh::lean_box((v___x_4778_) as usize);
                v___x_4795_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4795_, 0, v___x_4793_);
                leanh::lean_ctor_set(v___x_4795_, 1, v___x_4794_);
                v___x_4796_ = leanh::lean_box((v___x_4778_) as usize);
                v___x_4797_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4797_, 0, v___x_4796_);
                leanh::lean_ctor_set(v___x_4797_, 1, v___x_4795_);
                v___x_4798_ = leanh::lean_box((v___x_4778_) as usize);
                v___x_4799_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4799_, 0, v___x_4798_);
                leanh::lean_ctor_set(v___x_4799_, 1, v___x_4797_);
                v___x_4800_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4800_, 0, v___x_4790_);
                leanh::lean_ctor_set(v___x_4800_, 1, v___x_4799_);
                v___x_4801_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4801_, 0, v___x_4789_);
                leanh::lean_ctor_set(v___x_4801_, 1, v___x_4800_);
                v___x_4802_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg(v___x_4792_, v___x_4801_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
                if leanh::lean_obj_tag(v___x_4802_) == 0 {
                    v_a_4803_ = leanh::lean_ctor_get(v___x_4802_, 0);
                    v_isSharedCheck_4866_ = (!leanh::lean_is_exclusive(v___x_4802_)) as u8;
                    if v_isSharedCheck_4866_ == 0 {
                        v___x_4805_ = v___x_4802_;
                        v_isShared_4806_ = v_isSharedCheck_4866_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4803_);
                        leanh::lean_dec(v___x_4802_);
                        v___x_4805_ = leanh::lean_box(0);
                        v_isShared_4806_ = v_isSharedCheck_4866_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_4781_);
                    leanh::lean_dec(v_cidx_4780_);
                    leanh::lean_dec(v_ctorName_4779_);
                    v_a_4867_ = leanh::lean_ctor_get(v___x_4802_, 0);
                    v_isSharedCheck_4874_ = (!leanh::lean_is_exclusive(v___x_4802_)) as u8;
                    if v_isSharedCheck_4874_ == 0 {
                        v___x_4869_ = v___x_4802_;
                        v_isShared_4870_ = v_isSharedCheck_4874_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4867_);
                        leanh::lean_dec(v___x_4802_);
                        v___x_4869_ = leanh::lean_box(0);
                        v_isShared_4870_ = v_isSharedCheck_4874_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_4807_ = leanh::lean_ctor_get(v_a_4803_, 1);
                leanh::lean_inc(v_snd_4807_);
                v_fst_4808_ = leanh::lean_ctor_get(v_a_4803_, 0);
                leanh::lean_inc(v_fst_4808_);
                leanh::lean_dec(v_a_4803_);
                v_fst_4809_ = leanh::lean_ctor_get(v_snd_4807_, 0);
                leanh::lean_inc_n(v_fst_4809_, 2);
                v_snd_4810_ = leanh::lean_ctor_get(v_snd_4807_, 1);
                leanh::lean_inc(v_snd_4810_);
                leanh::lean_dec(v_snd_4807_);
                v_sz_4811_ = lean_array_size(v_fst_4808_);
                v___x_4812_ = 0usize;
                v___x_4813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__4(v_sz_4811_, v___x_4812_, v_fst_4808_, v_fst_4809_);
                v_snd_4814_ = leanh::lean_ctor_get(v_snd_4810_, 1);
                leanh::lean_inc(v_snd_4814_);
                v_snd_4815_ = leanh::lean_ctor_get(v_snd_4814_, 1);
                leanh::lean_inc(v_snd_4815_);
                v_fst_4816_ = leanh::lean_ctor_get(v___x_4813_, 0);
                leanh::lean_inc(v_fst_4816_);
                v_snd_4817_ = leanh::lean_ctor_get(v___x_4813_, 1);
                leanh::lean_inc(v_snd_4817_);
                leanh::lean_dec_ref(v___x_4813_);
                v_fst_4818_ = leanh::lean_ctor_get(v_snd_4810_, 0);
                leanh::lean_inc(v_fst_4818_);
                leanh::lean_dec(v_snd_4810_);
                v_fst_4819_ = leanh::lean_ctor_get(v_snd_4814_, 0);
                leanh::lean_inc(v_fst_4819_);
                leanh::lean_dec(v_snd_4814_);
                v_fst_4820_ = leanh::lean_ctor_get(v_snd_4815_, 0);
                v_snd_4821_ = leanh::lean_ctor_get(v_snd_4815_, 1);
                v_isSharedCheck_4865_ = (!leanh::lean_is_exclusive(v_snd_4815_)) as u8;
                if v_isSharedCheck_4865_ == 0 {
                    v___x_4823_ = v_snd_4815_;
                    v_isShared_4824_ = v_isSharedCheck_4865_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4821_);
                    leanh::lean_inc(v_fst_4820_);
                    leanh::lean_dec(v_snd_4815_);
                    v___x_4823_ = leanh::lean_box(0);
                    v_isShared_4824_ = v_isSharedCheck_4865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4825_ = lean_nat_sub(v_snd_4817_, v_fst_4809_);
                leanh::lean_dec(v_snd_4817_);
                v___x_4860_ = (leanh::lean_unbox(v_snd_4821_) as u8);
                leanh::lean_dec(v_snd_4821_);
                if v___x_4860_ == 0 {
                    v_fields_4853_ = v_fst_4816_;
                    v_nextOffset_4854_ = v___x_4790_;
                    state = 8;
                    continue;
                } else {
                    v___x_4861_ = leanh::lean_unsigned_to_nat(8);
                    leanh::lean_inc_ref(v___f_4781_);
                    v___x_4862_ = leanh::lean_apply_3(
                        v___f_4781_,
                        v_fst_4816_,
                        v___x_4861_,
                        v___x_4790_,
                    );
                    v_fst_4863_ = leanh::lean_ctor_get(v___x_4862_, 0);
                    leanh::lean_inc(v_fst_4863_);
                    v_snd_4864_ = leanh::lean_ctor_get(v___x_4862_, 1);
                    leanh::lean_inc(v_snd_4864_);
                    leanh::lean_dec_ref(v___x_4862_);
                    v_fields_4853_ = v_fst_4863_;
                    v_nextOffset_4854_ = v_snd_4864_;
                    state = 8;
                    continue;
                }
            }
            3 => {
                v___x_4829_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_4829_, 0, v_ctorName_4779_);
                leanh::lean_ctor_set(v___x_4829_, 1, v_cidx_4780_);
                leanh::lean_ctor_set(v___x_4829_, 2, v_fst_4809_);
                leanh::lean_ctor_set(v___x_4829_, 3, v___x_4825_);
                leanh::lean_ctor_set(v___x_4829_, 4, v_nextOffset_4828_);
                if v_isShared_4824_ == 0 {
                    leanh::lean_ctor_set(v___x_4823_, 1, v_fields_4827_);
                    leanh::lean_ctor_set(v___x_4823_, 0, v___x_4829_);
                    v___x_4831_ = v___x_4823_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4835_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_fields_4827_);
                    v___x_4831_ = v_reuseFailAlloc_4835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4806_ == 0 {
                    leanh::lean_ctor_set(v___x_4805_, 0, v___x_4831_);
                    v___x_4833_ = v___x_4805_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4834_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4834_, 0, v___x_4831_);
                    v___x_4833_ = v_reuseFailAlloc_4834_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4833_;
            }
            6 => {
                v___x_4839_ = (leanh::lean_unbox(v_fst_4818_) as u8);
                leanh::lean_dec(v_fst_4818_);
                if v___x_4839_ == 0 {
                    leanh::lean_dec_ref(v___f_4781_);
                    v_fields_4827_ = v_fields_4837_;
                    v_nextOffset_4828_ = v_nextOffset_4838_;
                    state = 3;
                    continue;
                } else {
                    v___x_4840_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4841_ = leanh::lean_apply_3(
                        v___f_4781_,
                        v_fields_4837_,
                        v___x_4840_,
                        v_nextOffset_4838_,
                    );
                    v_fst_4842_ = leanh::lean_ctor_get(v___x_4841_, 0);
                    leanh::lean_inc(v_fst_4842_);
                    v_snd_4843_ = leanh::lean_ctor_get(v___x_4841_, 1);
                    leanh::lean_inc(v_snd_4843_);
                    leanh::lean_dec_ref(v___x_4841_);
                    v_fields_4827_ = v_fst_4842_;
                    v_nextOffset_4828_ = v_snd_4843_;
                    state = 3;
                    continue;
                }
            }
            7 => {
                v___x_4847_ = (leanh::lean_unbox(v_fst_4819_) as u8);
                leanh::lean_dec(v_fst_4819_);
                if v___x_4847_ == 0 {
                    v_fields_4837_ = v_fields_4845_;
                    v_nextOffset_4838_ = v_nextOffset_4846_;
                    state = 6;
                    continue;
                } else {
                    v___x_4848_ = leanh::lean_unsigned_to_nat(2);
                    leanh::lean_inc_ref(v___f_4781_);
                    v___x_4849_ = leanh::lean_apply_3(
                        v___f_4781_,
                        v_fields_4845_,
                        v___x_4848_,
                        v_nextOffset_4846_,
                    );
                    v_fst_4850_ = leanh::lean_ctor_get(v___x_4849_, 0);
                    leanh::lean_inc(v_fst_4850_);
                    v_snd_4851_ = leanh::lean_ctor_get(v___x_4849_, 1);
                    leanh::lean_inc(v_snd_4851_);
                    leanh::lean_dec_ref(v___x_4849_);
                    v_fields_4837_ = v_fst_4850_;
                    v_nextOffset_4838_ = v_snd_4851_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_4855_ = (leanh::lean_unbox(v_fst_4820_) as u8);
                leanh::lean_dec(v_fst_4820_);
                if v___x_4855_ == 0 {
                    v_fields_4845_ = v_fields_4853_;
                    v_nextOffset_4846_ = v_nextOffset_4854_;
                    state = 7;
                    continue;
                } else {
                    v___x_4856_ = leanh::lean_unsigned_to_nat(4);
                    leanh::lean_inc_ref(v___f_4781_);
                    v___x_4857_ = leanh::lean_apply_3(
                        v___f_4781_,
                        v_fields_4853_,
                        v___x_4856_,
                        v_nextOffset_4854_,
                    );
                    v_fst_4858_ = leanh::lean_ctor_get(v___x_4857_, 0);
                    leanh::lean_inc(v_fst_4858_);
                    v_snd_4859_ = leanh::lean_ctor_get(v___x_4857_, 1);
                    leanh::lean_inc(v_snd_4859_);
                    leanh::lean_dec_ref(v___x_4857_);
                    v_fields_4845_ = v_fst_4858_;
                    v_nextOffset_4846_ = v_snd_4859_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v_isShared_4870_ == 0 {
                    v___x_4872_ = v___x_4869_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4873_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
                    v___x_4872_ = v_reuseFailAlloc_4873_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___lam__1___boxed(
    mut v_numFields_4875_: *mut leanh::LeanObject,
    mut v_numParams_4876_: *mut leanh::LeanObject,
    mut v___x_4877_: *mut leanh::LeanObject,
    mut v_ctorName_4878_: *mut leanh::LeanObject,
    mut v_cidx_4879_: *mut leanh::LeanObject,
    mut v___f_4880_: *mut leanh::LeanObject,
    mut v_params_4881_: *mut leanh::LeanObject,
    mut v_x_4882_: *mut leanh::LeanObject,
    mut v___y_4883_: *mut leanh::LeanObject,
    mut v___y_4884_: *mut leanh::LeanObject,
    mut v___y_4885_: *mut leanh::LeanObject,
    mut v___y_4886_: *mut leanh::LeanObject,
    mut v___y_4887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_13731__boxed_4888_: u8 = 0;
    let mut v_res_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_13731__boxed_4888_ = (leanh::lean_unbox(v___x_4877_) as u8);
    v_res_4889_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___lam__1(v_numFields_4875_, v_numParams_4876_, v___x_13731__boxed_4888_, v_ctorName_4878_, v_cidx_4879_, v___f_4880_, v_params_4881_, v_x_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
    leanh::lean_dec(v___y_4886_);
    leanh::lean_dec_ref(v___y_4885_);
    leanh::lean_dec(v___y_4884_);
    leanh::lean_dec_ref(v___y_4883_);
    leanh::lean_dec_ref(v_x_4882_);
    leanh::lean_dec(v_numFields_4875_);
    return v_res_4889_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4890_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__2;
    v___x_4891_ = leanh::lean_unsigned_to_nat(64);
    v___x_4892_ = leanh::lean_unsigned_to_nat(163);
    v___x_4893_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg___lam__1___closed__0;
    v___x_4894_ = l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__0;
    v___x_4895_ = l_mkPanicMessageWithDecl(
        v___x_4894_,
        v___x_4893_,
        v___x_4892_,
        v___x_4891_,
        v___x_4890_,
    );
    return v___x_4895_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache(
    mut v_ctorName_4897_: *mut leanh::LeanObject,
    mut v_a_4898_: *mut leanh::LeanObject,
    mut v_a_4899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: u8 = 0;
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4906_ = lean_st_ref_get(v_a_4899_);
                v_env_4907_ = leanh::lean_ctor_get(v___x_4906_, 0);
                leanh::lean_inc_ref(v_env_4907_);
                leanh::lean_dec(v___x_4906_);
                v___x_4908_ = 0;
                leanh::lean_inc(v_ctorName_4897_);
                v___x_4909_ =
                    l_Lean_Environment_find_x3f(v_env_4907_, v_ctorName_4897_, v___x_4908_);
                if leanh::lean_obj_tag(v___x_4909_) == 1 {
                    v_val_4910_ = leanh::lean_ctor_get(v___x_4909_, 0);
                    leanh::lean_inc(v_val_4910_);
                    leanh::lean_dec_ref_known(v___x_4909_, 1);
                    if leanh::lean_obj_tag(v_val_4910_) == 6 {
                        v_val_4911_ = leanh::lean_ctor_get(v_val_4910_, 0);
                        leanh::lean_inc_ref(v_val_4911_);
                        leanh::lean_dec_ref_known(v_val_4910_, 1);
                        v___x_4912_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__13), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__13_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__13);
                        v___x_4913_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__17), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__17_once), _init_l_List_forIn_x27_loop___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_nameToImpureType_fillCache_spec__3___redArg___closed__17);
                        v___x_4914_ = lean_st_mk_ref(v___x_4913_);
                        v_toConstantVal_4915_ = leanh::lean_ctor_get(v_val_4911_, 0);
                        leanh::lean_inc_ref(v_toConstantVal_4915_);
                        v_cidx_4916_ = leanh::lean_ctor_get(v_val_4911_, 2);
                        leanh::lean_inc(v_cidx_4916_);
                        v_numParams_4917_ = leanh::lean_ctor_get(v_val_4911_, 3);
                        leanh::lean_inc(v_numParams_4917_);
                        v_numFields_4918_ = leanh::lean_ctor_get(v_val_4911_, 4);
                        leanh::lean_inc(v_numFields_4918_);
                        leanh::lean_dec_ref(v_val_4911_);
                        v_type_4919_ = leanh::lean_ctor_get(v_toConstantVal_4915_, 2);
                        leanh::lean_inc_ref(v_type_4919_);
                        leanh::lean_dec_ref(v_toConstantVal_4915_);
                        v___f_4920_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___closed__1;
                        v___x_4921_ = leanh::lean_box((v___x_4908_) as usize);
                        v___f_4922_ = leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___lam__1___boxed as *mut core::ffi::c_void, 13, 6);
                        leanh::lean_closure_set(v___f_4922_, 0, v_numFields_4918_);
                        leanh::lean_closure_set(v___f_4922_, 1, v_numParams_4917_);
                        leanh::lean_closure_set(v___f_4922_, 2, v___x_4921_);
                        leanh::lean_closure_set(v___f_4922_, 3, v_ctorName_4897_);
                        leanh::lean_closure_set(v___f_4922_, 4, v_cidx_4916_);
                        leanh::lean_closure_set(v___f_4922_, 5, v___f_4920_);
                        v___x_4923_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__5___redArg(v_type_4919_, v___f_4922_, v___x_4908_, v___x_4908_, v___x_4912_, v___x_4914_, v_a_4898_, v_a_4899_);
                        if leanh::lean_obj_tag(v___x_4923_) == 0 {
                            v_a_4924_ = leanh::lean_ctor_get(v___x_4923_, 0);
                            v_isSharedCheck_4932_ =
                                (!leanh::lean_is_exclusive(v___x_4923_)) as u8;
                            if v_isSharedCheck_4932_ == 0 {
                                v___x_4926_ = v___x_4923_;
                                v_isShared_4927_ = v_isSharedCheck_4932_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4924_);
                                leanh::lean_dec(v___x_4923_);
                                v___x_4926_ = leanh::lean_box(0);
                                v_isShared_4927_ = v_isSharedCheck_4932_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_4914_);
                            return v___x_4923_;
                        }
                    } else {
                        leanh::lean_dec(v_val_4910_);
                        leanh::lean_dec(v_ctorName_4897_);
                        v___y_4902_ = v_a_4898_;
                        v___y_4903_ = v_a_4899_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4909_);
                    leanh::lean_dec(v_ctorName_4897_);
                    v___y_4902_ = v_a_4898_;
                    v___y_4903_ = v_a_4899_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4904_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___closed__0_once), _init_l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___closed__0);
                v___x_4905_ = l_panic___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__1(v___x_4904_, v___y_4902_, v___y_4903_);
                return v___x_4905_;
            }
            2 => {
                v___x_4928_ = lean_st_ref_get(v___x_4914_);
                leanh::lean_dec(v___x_4914_);
                leanh::lean_dec(v___x_4928_);
                if v_isShared_4927_ == 0 {
                    v___x_4930_ = v___x_4926_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4931_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4924_);
                    v___x_4930_ = v_reuseFailAlloc_4931_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache___boxed(
    mut v_ctorName_4933_: *mut leanh::LeanObject,
    mut v_a_4934_: *mut leanh::LeanObject,
    mut v_a_4935_: *mut leanh::LeanObject,
    mut v_a_4936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4937_ =
        l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache(
            v_ctorName_4933_,
            v_a_4934_,
            v_a_4935_,
        );
    leanh::lean_dec(v_a_4935_);
    leanh::lean_dec_ref(v_a_4934_);
    return v_res_4937_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3(
    mut v_inst_4938_: *mut leanh::LeanObject,
    mut v_R_4939_: *mut leanh::LeanObject,
    mut v_a_4940_: *mut leanh::LeanObject,
    mut v_b_4941_: *mut leanh::LeanObject,
    mut v_c_4942_: *mut leanh::LeanObject,
    mut v___y_4943_: *mut leanh::LeanObject,
    mut v___y_4944_: *mut leanh::LeanObject,
    mut v___y_4945_: *mut leanh::LeanObject,
    mut v___y_4946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___redArg(v_a_4940_, v_b_4941_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_);
    return v___x_4948_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3___boxed(
    mut v_inst_4949_: *mut leanh::LeanObject,
    mut v_R_4950_: *mut leanh::LeanObject,
    mut v_a_4951_: *mut leanh::LeanObject,
    mut v_b_4952_: *mut leanh::LeanObject,
    mut v_c_4953_: *mut leanh::LeanObject,
    mut v___y_4954_: *mut leanh::LeanObject,
    mut v___y_4955_: *mut leanh::LeanObject,
    mut v___y_4956_: *mut leanh::LeanObject,
    mut v___y_4957_: *mut leanh::LeanObject,
    mut v___y_4958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4959_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache_spec__3(v_inst_4949_, v_R_4950_, v_a_4951_, v_b_4952_, v_c_4953_, v___y_4954_, v___y_4955_, v___y_4956_, v___y_4957_);
    leanh::lean_dec(v___y_4957_);
    leanh::lean_dec_ref(v___y_4956_);
    leanh::lean_dec(v___y_4955_);
    leanh::lean_dec_ref(v___y_4954_);
    return v_res_4959_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4960_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__1;
    v___x_4961_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_nameToImpureType_spec__0___redArg___closed__0;
    v___x_4962_ = l_Lean_PersistentHashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4961_,
        v___x_4960_,
    );
    return v___x_4962_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4963_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__0_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__0);
    v___x_4964_ = leanh::lean_box(0);
    v___x_4965_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4965_, 0, v___x_4964_);
    leanh::lean_ctor_set(v___x_4965_, 1, v___x_4963_);
    return v___x_4965_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg(
    mut v_ext_4966_: *mut leanh::LeanObject,
    mut v_a_4967_: *mut leanh::LeanObject,
    mut v_a_4968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4970_ = lean_st_ref_get(v_a_4968_);
    v_env_4971_ = leanh::lean_ctor_get(v___x_4970_, 0);
    leanh::lean_inc_ref(v_env_4971_);
    leanh::lean_dec(v___x_4970_);
    v_asyncMode_4972_ = leanh::lean_ctor_get(v_ext_4966_, 2);
    v___x_4973_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___closed__1);
    v___x_4974_ = leanh::lean_box(0);
    v___x_4975_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_4973_,
        v_ext_4966_,
        v_env_4971_,
        v_asyncMode_4972_,
        v___x_4974_,
    );
    v_snd_4976_ = leanh::lean_ctor_get(v___x_4975_, 1);
    leanh::lean_inc(v_snd_4976_);
    leanh::lean_dec(v___x_4975_);
    v___x_4977_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_4976_, v_a_4967_);
    leanh::lean_dec(v_snd_4976_);
    v___x_4978_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4978_, 0, v___x_4977_);
    return v___x_4978_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg___boxed(
    mut v_ext_4979_: *mut leanh::LeanObject,
    mut v_a_4980_: *mut leanh::LeanObject,
    mut v_a_4981_: *mut leanh::LeanObject,
    mut v_a_4982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4983_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg(v_ext_4979_, v_a_4980_, v_a_4981_);
    leanh::lean_dec(v_a_4981_);
    leanh::lean_dec(v_a_4980_);
    leanh::lean_dec_ref(v_ext_4979_);
    return v_res_4983_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getCtorLayout_spec__1___redArg___lam__0(
    mut v_a_4984_: *mut leanh::LeanObject,
    mut v_b_4985_: *mut leanh::LeanObject,
    mut v_x_4986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4991_: u8 = 0;
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_4987_ = leanh::lean_ctor_get(v_x_4986_, 0);
                v_snd_4988_ = leanh::lean_ctor_get(v_x_4986_, 1);
                v_isSharedCheck_4997_ = (!leanh::lean_is_exclusive(v_x_4986_)) as u8;
                if v_isSharedCheck_4997_ == 0 {
                    v___x_4990_ = v_x_4986_;
                    v_isShared_4991_ = v_isSharedCheck_4997_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4988_);
                    leanh::lean_inc(v_fst_4987_);
                    leanh::lean_dec(v_x_4986_);
                    v___x_4990_ = leanh::lean_box(0);
                    v_isShared_4991_ = v_isSharedCheck_4997_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_a_4984_);
                v___x_4992_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4992_, 0, v_a_4984_);
                leanh::lean_ctor_set(v___x_4992_, 1, v_fst_4987_);
                v___x_4993_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_4988_, v_a_4984_, v_b_4985_);
                if v_isShared_4991_ == 0 {
                    leanh::lean_ctor_set(v___x_4990_, 1, v___x_4993_);
                    leanh::lean_ctor_set(v___x_4990_, 0, v___x_4992_);
                    v___x_4995_ = v___x_4990_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4996_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4996_, 1, v___x_4993_);
                    v___x_4995_ = v_reuseFailAlloc_4996_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4995_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getCtorLayout_spec__1___redArg(
    mut v_ext_4998_: *mut leanh::LeanObject,
    mut v_a_4999_: *mut leanh::LeanObject,
    mut v_b_5000_: *mut leanh::LeanObject,
    mut v_a_5001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5014_: u8 = 0;
    let mut v_asyncMode_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5026_: u8 = 0;
    let mut v_unused_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5003_ = lean_st_ref_take(v_a_5001_);
                v_env_5004_ = leanh::lean_ctor_get(v___x_5003_, 0);
                v_nextMacroScope_5005_ = leanh::lean_ctor_get(v___x_5003_, 1);
                v_ngen_5006_ = leanh::lean_ctor_get(v___x_5003_, 2);
                v_auxDeclNGen_5007_ = leanh::lean_ctor_get(v___x_5003_, 3);
                v_traceState_5008_ = leanh::lean_ctor_get(v___x_5003_, 4);
                v_messages_5009_ = leanh::lean_ctor_get(v___x_5003_, 6);
                v_infoState_5010_ = leanh::lean_ctor_get(v___x_5003_, 7);
                v_snapshotTasks_5011_ = leanh::lean_ctor_get(v___x_5003_, 8);
                v_isSharedCheck_5026_ = (!leanh::lean_is_exclusive(v___x_5003_)) as u8;
                if v_isSharedCheck_5026_ == 0 {
                    v_unused_5027_ = leanh::lean_ctor_get(v___x_5003_, 5);
                    leanh::lean_dec(v_unused_5027_);
                    v___x_5013_ = v___x_5003_;
                    v_isShared_5014_ = v_isSharedCheck_5026_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5011_);
                    leanh::lean_inc(v_infoState_5010_);
                    leanh::lean_inc(v_messages_5009_);
                    leanh::lean_inc(v_traceState_5008_);
                    leanh::lean_inc(v_auxDeclNGen_5007_);
                    leanh::lean_inc(v_ngen_5006_);
                    leanh::lean_inc(v_nextMacroScope_5005_);
                    leanh::lean_inc(v_env_5004_);
                    leanh::lean_dec(v___x_5003_);
                    v___x_5013_ = leanh::lean_box(0);
                    v_isShared_5014_ = v_isSharedCheck_5026_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_asyncMode_5015_ = leanh::lean_ctor_get(v_ext_4998_, 2);
                leanh::lean_inc(v_asyncMode_5015_);
                v___f_5016_ = leanh::lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getCtorLayout_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_5016_, 0, v_a_4999_);
                leanh::lean_closure_set(v___f_5016_, 1, v_b_5000_);
                v___x_5017_ = leanh::lean_box(0);
                v___x_5018_ = l_Lean_EnvExtension_modifyState___redArg(
                    v_ext_4998_,
                    v_env_5004_,
                    v___f_5016_,
                    v_asyncMode_5015_,
                    v___x_5017_,
                );
                leanh::lean_dec(v_asyncMode_5015_);
                v___x_5019_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_nameToImpureType_spec__1___redArg___closed__2);
                if v_isShared_5014_ == 0 {
                    leanh::lean_ctor_set(v___x_5013_, 5, v___x_5019_);
                    leanh::lean_ctor_set(v___x_5013_, 0, v___x_5018_);
                    v___x_5021_ = v___x_5013_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5025_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5018_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5025_, 1, v_nextMacroScope_5005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5025_, 2, v_ngen_5006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5025_, 3, v_auxDeclNGen_5007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5025_, 4, v_traceState_5008_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5025_, 5, v___x_5019_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5025_, 6, v_messages_5009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5025_, 7, v_infoState_5010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5025_, 8, v_snapshotTasks_5011_);
                    v___x_5021_ = v_reuseFailAlloc_5025_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5022_ = lean_st_ref_set(v_a_5001_, v___x_5021_);
                v___x_5023_ = leanh::lean_box(0);
                v___x_5024_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5024_, 0, v___x_5023_);
                return v___x_5024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getCtorLayout_spec__1___redArg___boxed(
    mut v_ext_5028_: *mut leanh::LeanObject,
    mut v_a_5029_: *mut leanh::LeanObject,
    mut v_b_5030_: *mut leanh::LeanObject,
    mut v_a_5031_: *mut leanh::LeanObject,
    mut v_a_5032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5033_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getCtorLayout_spec__1___redArg(v_ext_5028_, v_a_5029_, v_b_5030_, v_a_5031_);
    leanh::lean_dec(v_a_5031_);
    return v_res_5033_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getCtorLayout(
    mut v_ctorName_5034_: *mut leanh::LeanObject,
    mut v_a_5035_: *mut leanh::LeanObject,
    mut v_a_5036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5043_: u8 = 0;
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5049_: u8 = 0;
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5053_: u8 = 0;
    let mut v_unused_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5038_ =
                    l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt;
                v___x_5039_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg(v___x_5038_, v_ctorName_5034_, v_a_5036_);
                v_a_5040_ = leanh::lean_ctor_get(v___x_5039_, 0);
                v_isSharedCheck_5059_ = (!leanh::lean_is_exclusive(v___x_5039_)) as u8;
                if v_isSharedCheck_5059_ == 0 {
                    v___x_5042_ = v___x_5039_;
                    v_isShared_5043_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5040_);
                    leanh::lean_dec(v___x_5039_);
                    v___x_5042_ = leanh::lean_box(0);
                    v_isShared_5043_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5040_) == 0 {
                    leanh::lean_del_object(v___x_5042_);
                    leanh::lean_inc(v_ctorName_5034_);
                    v___x_5044_ = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_getCtorLayout_fillCache(v_ctorName_5034_, v_a_5035_, v_a_5036_);
                    if leanh::lean_obj_tag(v___x_5044_) == 0 {
                        v_a_5045_ = leanh::lean_ctor_get(v___x_5044_, 0);
                        leanh::lean_inc_n(v_a_5045_, 2);
                        leanh::lean_dec_ref_known(v___x_5044_, 1);
                        v___x_5046_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getCtorLayout_spec__1___redArg(v___x_5038_, v_ctorName_5034_, v_a_5045_, v_a_5036_);
                        v_isSharedCheck_5053_ =
                            (!leanh::lean_is_exclusive(v___x_5046_)) as u8;
                        if v_isSharedCheck_5053_ == 0 {
                            v_unused_5054_ = leanh::lean_ctor_get(v___x_5046_, 0);
                            leanh::lean_dec(v_unused_5054_);
                            v___x_5048_ = v___x_5046_;
                            v_isShared_5049_ = v_isSharedCheck_5053_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5046_);
                            v___x_5048_ = leanh::lean_box(0);
                            v_isShared_5049_ = v_isSharedCheck_5053_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_ctorName_5034_);
                        return v___x_5044_;
                    }
                } else {
                    leanh::lean_dec(v_ctorName_5034_);
                    v_val_5055_ = leanh::lean_ctor_get(v_a_5040_, 0);
                    leanh::lean_inc(v_val_5055_);
                    leanh::lean_dec_ref_known(v_a_5040_, 1);
                    if v_isShared_5043_ == 0 {
                        leanh::lean_ctor_set(v___x_5042_, 0, v_val_5055_);
                        v___x_5057_ = v___x_5042_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5058_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_val_5055_);
                        v___x_5057_ = v_reuseFailAlloc_5058_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5049_ == 0 {
                    leanh::lean_ctor_set(v___x_5048_, 0, v_a_5045_);
                    v___x_5051_ = v___x_5048_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5052_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5045_);
                    v___x_5051_ = v_reuseFailAlloc_5052_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5051_;
            }
            4 => {
                return v___x_5057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getCtorLayout___boxed(
    mut v_ctorName_5060_: *mut leanh::LeanObject,
    mut v_a_5061_: *mut leanh::LeanObject,
    mut v_a_5062_: *mut leanh::LeanObject,
    mut v_a_5063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5064_ = l_Lean_Compiler_LCNF_getCtorLayout(v_ctorName_5060_, v_a_5061_, v_a_5062_);
    leanh::lean_dec(v_a_5062_);
    leanh::lean_dec_ref(v_a_5061_);
    return v_res_5064_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0(
    mut v_ext_5065_: *mut leanh::LeanObject,
    mut v_a_5066_: *mut leanh::LeanObject,
    mut v_a_5067_: *mut leanh::LeanObject,
    mut v_a_5068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5070_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___redArg(v_ext_5065_, v_a_5066_, v_a_5068_);
    return v___x_5070_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0___boxed(
    mut v_ext_5071_: *mut leanh::LeanObject,
    mut v_a_5072_: *mut leanh::LeanObject,
    mut v_a_5073_: *mut leanh::LeanObject,
    mut v_a_5074_: *mut leanh::LeanObject,
    mut v_a_5075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5076_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getCtorLayout_spec__0(v_ext_5071_, v_a_5072_, v_a_5073_, v_a_5074_);
    leanh::lean_dec(v_a_5074_);
    leanh::lean_dec_ref(v_a_5073_);
    leanh::lean_dec(v_a_5072_);
    leanh::lean_dec_ref(v_ext_5071_);
    return v_res_5076_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getCtorLayout_spec__1(
    mut v_ext_5077_: *mut leanh::LeanObject,
    mut v_a_5078_: *mut leanh::LeanObject,
    mut v_b_5079_: *mut leanh::LeanObject,
    mut v_a_5080_: *mut leanh::LeanObject,
    mut v_a_5081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5083_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getCtorLayout_spec__1___redArg(v_ext_5077_, v_a_5078_, v_b_5079_, v_a_5081_);
    return v___x_5083_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getCtorLayout_spec__1___boxed(
    mut v_ext_5084_: *mut leanh::LeanObject,
    mut v_a_5085_: *mut leanh::LeanObject,
    mut v_b_5086_: *mut leanh::LeanObject,
    mut v_a_5087_: *mut leanh::LeanObject,
    mut v_a_5088_: *mut leanh::LeanObject,
    mut v_a_5089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5090_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getCtorLayout_spec__1(v_ext_5084_, v_a_5085_, v_b_5086_, v_a_5087_, v_a_5088_);
    leanh::lean_dec(v_a_5088_);
    leanh::lean_dec_ref(v_a_5087_);
    return v_res_5090_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ToImpureType(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_3556920009____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTypeExt,
    );
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_1057723166____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_impureTrivialStructureInfoExt);
    leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo_default);
    l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo =
        _init_l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCtorFieldInfo);
    l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default =
        _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCtorLayout_default);
    l_Lean_Compiler_LCNF_instInhabitedCtorLayout =
        _init_l_Lean_Compiler_LCNF_instInhabitedCtorLayout();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_instInhabitedCtorLayout);
    res = l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ToImpureType_4224556303____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_Compiler_LCNF_ToImpureType_0__Lean_Compiler_LCNF_ctorLayoutExt,
    );
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ToImpureType(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_ToImpureType(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Format_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
}