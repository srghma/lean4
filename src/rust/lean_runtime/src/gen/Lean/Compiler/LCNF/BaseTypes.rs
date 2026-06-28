// Lean compiler output
// Module: Lean.Compiler.LCNF.BaseTypes
// Imports: Lean.Compiler.LCNF.CompilerM
use crate::r#gen::Init::Data::List::Impl::l___private_Init_Data_List_Impl_0__List_takeTR_go;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_replaceRef,
    l_List_lengthTR___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::l_Lean_Compiler_LCNF_toLCNFType;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg, l_Lean_PersistentHashMap_instInhabited,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::{l_Lean_ConstantInfo_levelParams, l_Lean_ConstantInfo_type};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_EnvExtension_modifyState___redArg, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_registerEnvExtension___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::l_Lean_instInhabitedExpr;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::InstantiateLevelParams::l_Lean_Expr_instantiateLevelParamsNoCache;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__0_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__0_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__1_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [76, 101, 97, 110, 46, 80, 101, 114, 115, 105, 115, 116, 101, 110, 116, 72, 97, 115, 104, 77, 97, 112, 46, 102, 105, 110, 100, 33, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [107, 101, 121, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 32, 116, 104, 101, 32, 109, 97, 112, 0]};
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__5_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 24) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [
            282574488338432 as *mut LeanObject,
            72621647814721793 as *mut LeanObject,
            65793 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__1: u64 = 0;
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__6_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__1(
    mut v___x_961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    v___x_963_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_963_, 0, v___x_961_);
    return v___x_963_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__1___boxed(
    mut v___x_964_: *mut LeanObject,
    mut v___y_965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_966_: *mut LeanObject = core::ptr::null_mut();
    v_res_966_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__1(v___x_964_);
    return v_res_966_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_x_967_: *mut LeanObject,
    mut v_x_968_: *mut LeanObject,
    mut v_x_969_: *mut LeanObject,
    mut v_x_970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_975_: u8 = 0;
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: u8 = 0;
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u8 = 0;
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_971_ = lean_ctor_get(v_x_967_, 0);
                v_vs_972_ = lean_ctor_get(v_x_967_, 1);
                v_isSharedCheck_996_ = (!lean_is_exclusive(v_x_967_)) as u8;
                if v_isSharedCheck_996_ == 0 {
                    v___x_974_ = v_x_967_;
                    v_isShared_975_ = v_isSharedCheck_996_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_972_);
                    lean_inc(v_ks_971_);
                    lean_dec(v_x_967_);
                    v___x_974_ = lean_box(0);
                    v_isShared_975_ = v_isSharedCheck_996_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_976_ = lean_array_get_size(v_ks_971_);
                v___x_977_ = lean_nat_dec_lt(v_x_968_, v___x_976_);
                if v___x_977_ == 0 {
                    lean_dec(v_x_968_);
                    v___x_978_ = lean_array_push(v_ks_971_, v_x_969_);
                    v___x_979_ = lean_array_push(v_vs_972_, v_x_970_);
                    if v_isShared_975_ == 0 {
                        lean_ctor_set(v___x_974_, 1, v___x_979_);
                        lean_ctor_set(v___x_974_, 0, v___x_978_);
                        v___x_981_ = v___x_974_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_978_);
                        lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_979_);
                        v___x_981_ = v_reuseFailAlloc_982_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_983_ = lean_array_fget_borrowed(v_ks_971_, v_x_968_);
                    v___x_984_ = lean_name_eq(v_x_969_, v_k_x27_983_);
                    if v___x_984_ == 0 {
                        if v_isShared_975_ == 0 {
                            v___x_986_ = v___x_974_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_990_, 0, v_ks_971_);
                            lean_ctor_set(v_reuseFailAlloc_990_, 1, v_vs_972_);
                            v___x_986_ = v_reuseFailAlloc_990_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_991_ = lean_array_fset(v_ks_971_, v_x_968_, v_x_969_);
                        v___x_992_ = lean_array_fset(v_vs_972_, v_x_968_, v_x_970_);
                        lean_dec(v_x_968_);
                        if v_isShared_975_ == 0 {
                            lean_ctor_set(v___x_974_, 1, v___x_992_);
                            lean_ctor_set(v___x_974_, 0, v___x_991_);
                            v___x_994_ = v___x_974_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_991_);
                            lean_ctor_set(v_reuseFailAlloc_995_, 1, v___x_992_);
                            v___x_994_ = v_reuseFailAlloc_995_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_981_;
            }
            3 => {
                v___x_987_ = lean_unsigned_to_nat(1);
                v___x_988_ = lean_nat_add(v_x_968_, v___x_987_);
                lean_dec(v_x_968_);
                v_x_967_ = v___x_986_;
                v_x_968_ = v___x_988_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_n_997_: *mut LeanObject,
    mut v_k_998_: *mut LeanObject,
    mut v_v_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    v___x_1000_ = lean_unsigned_to_nat(0);
    v___x_1001_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_n_997_, v___x_1000_, v_k_998_, v_v_999_);
    return v___x_1001_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0()
-> u64 {
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u64 = 0;
    v___x_1002_ = lean_unsigned_to_nat(1723);
    v___x_1003_ = lean_uint64_of_nat(v___x_1002_);
    return v___x_1003_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_1004_: usize = 0;
    let mut v___x_1005_: usize = 0;
    let mut v___x_1006_: usize = 0;
    v___x_1004_ = 5usize;
    v___x_1005_ = 1usize;
    v___x_1006_ = lean_usize_shift_left(v___x_1005_, v___x_1004_);
    return v___x_1006_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_1007_: usize = 0;
    let mut v___x_1008_: usize = 0;
    let mut v___x_1009_: usize = 0;
    v___x_1007_ = 1usize;
    v___x_1008_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_1009_ = lean_usize_sub(v___x_1008_, v___x_1007_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    v___x_1010_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1010_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_x_1011_: *mut LeanObject,
    mut v_x_1012_: usize,
    mut v_x_1013_: usize,
    mut v_x_1014_: *mut LeanObject,
    mut v_x_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: usize = 0;
    let mut v___x_1018_: usize = 0;
    let mut v___x_1019_: usize = 0;
    let mut v___x_1020_: usize = 0;
    let mut v_j_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: u8 = 0;
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1026_: u8 = 0;
    let mut v_v_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1040_: u8 = 0;
    let mut v___x_1041_: u8 = 0;
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1047_: u8 = 0;
    let mut v_node_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1051_: u8 = 0;
    let mut v___x_1052_: usize = 0;
    let mut v___x_1053_: usize = 0;
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1058_: u8 = 0;
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_unused_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1071_: u8 = 0;
    let mut v_ks_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: usize = 0;
    let mut v___x_1078_: u8 = 0;
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: u8 = 0;
    let mut v_reuseFailAlloc_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1011_) == 0 {
                    v_es_1016_ = lean_ctor_get(v_x_1011_, 0);
                    v___x_1017_ = 5usize;
                    v___x_1018_ = 1usize;
                    v___x_1019_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_1020_ = lean_usize_land(v_x_1012_, v___x_1019_);
                    v_j_1021_ = lean_usize_to_nat(v___x_1020_);
                    v___x_1022_ = lean_array_get_size(v_es_1016_);
                    v___x_1023_ = lean_nat_dec_lt(v_j_1021_, v___x_1022_);
                    if v___x_1023_ == 0 {
                        lean_dec(v_j_1021_);
                        lean_dec(v_x_1015_);
                        lean_dec(v_x_1014_);
                        return v_x_1011_;
                    } else {
                        lean_inc_ref(v_es_1016_);
                        v_isSharedCheck_1060_ = (!lean_is_exclusive(v_x_1011_)) as u8;
                        if v_isSharedCheck_1060_ == 0 {
                            v_unused_1061_ = lean_ctor_get(v_x_1011_, 0);
                            lean_dec(v_unused_1061_);
                            v___x_1025_ = v_x_1011_;
                            v_isShared_1026_ = v_isSharedCheck_1060_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1011_);
                            v___x_1025_ = lean_box(0);
                            v_isShared_1026_ = v_isSharedCheck_1060_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1062_ = lean_ctor_get(v_x_1011_, 0);
                    v_vs_1063_ = lean_ctor_get(v_x_1011_, 1);
                    v_isSharedCheck_1083_ = (!lean_is_exclusive(v_x_1011_)) as u8;
                    if v_isSharedCheck_1083_ == 0 {
                        v___x_1065_ = v_x_1011_;
                        v_isShared_1066_ = v_isSharedCheck_1083_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1063_);
                        lean_inc(v_ks_1062_);
                        lean_dec(v_x_1011_);
                        v___x_1065_ = lean_box(0);
                        v_isShared_1066_ = v_isSharedCheck_1083_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1027_ = lean_array_fget(v_es_1016_, v_j_1021_);
                v___x_1028_ = lean_box(0);
                v_xs_x27_1029_ = lean_array_fset(v_es_1016_, v_j_1021_, v___x_1028_);
                match lean_obj_tag(v_v_1027_) {
                    0 => {
                        v_key_1036_ = lean_ctor_get(v_v_1027_, 0);
                        v_val_1037_ = lean_ctor_get(v_v_1027_, 1);
                        v_isSharedCheck_1047_ = (!lean_is_exclusive(v_v_1027_)) as u8;
                        if v_isSharedCheck_1047_ == 0 {
                            v___x_1039_ = v_v_1027_;
                            v_isShared_1040_ = v_isSharedCheck_1047_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1037_);
                            lean_inc(v_key_1036_);
                            lean_dec(v_v_1027_);
                            v___x_1039_ = lean_box(0);
                            v_isShared_1040_ = v_isSharedCheck_1047_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1048_ = lean_ctor_get(v_v_1027_, 0);
                        v_isSharedCheck_1058_ = (!lean_is_exclusive(v_v_1027_)) as u8;
                        if v_isSharedCheck_1058_ == 0 {
                            v___x_1050_ = v_v_1027_;
                            v_isShared_1051_ = v_isSharedCheck_1058_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1048_);
                            lean_dec(v_v_1027_);
                            v___x_1050_ = lean_box(0);
                            v_isShared_1051_ = v_isSharedCheck_1058_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1059_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1059_, 0, v_x_1014_);
                        lean_ctor_set(v___x_1059_, 1, v_x_1015_);
                        v___y_1031_ = v___x_1059_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1032_ = lean_array_fset(v_xs_x27_1029_, v_j_1021_, v___y_1031_);
                lean_dec(v_j_1021_);
                if v_isShared_1026_ == 0 {
                    lean_ctor_set(v___x_1025_, 0, v___x_1032_);
                    v___x_1034_ = v___x_1025_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
                    v___x_1034_ = v_reuseFailAlloc_1035_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1034_;
            }
            4 => {
                v___x_1041_ = lean_name_eq(v_x_1014_, v_key_1036_);
                if v___x_1041_ == 0 {
                    lean_del_object(v___x_1039_);
                    v___x_1042_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1036_,
                        v_val_1037_,
                        v_x_1014_,
                        v_x_1015_,
                    );
                    v___x_1043_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1043_, 0, v___x_1042_);
                    v___y_1031_ = v___x_1043_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1037_);
                    lean_dec(v_key_1036_);
                    if v_isShared_1040_ == 0 {
                        lean_ctor_set(v___x_1039_, 1, v_x_1015_);
                        lean_ctor_set(v___x_1039_, 0, v_x_1014_);
                        v___x_1045_ = v___x_1039_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_x_1014_);
                        lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_x_1015_);
                        v___x_1045_ = v_reuseFailAlloc_1046_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1031_ = v___x_1045_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1052_ = lean_usize_shift_right(v_x_1012_, v___x_1017_);
                v___x_1053_ = lean_usize_add(v_x_1013_, v___x_1018_);
                v___x_1054_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_node_1048_, v___x_1052_, v___x_1053_, v_x_1014_, v_x_1015_);
                if v_isShared_1051_ == 0 {
                    lean_ctor_set(v___x_1050_, 0, v___x_1054_);
                    v___x_1056_ = v___x_1050_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
                    v___x_1056_ = v_reuseFailAlloc_1057_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1031_ = v___x_1056_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1066_ == 0 {
                    v___x_1068_ = v___x_1065_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_ks_1062_);
                    lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_vs_1063_);
                    v___x_1068_ = v_reuseFailAlloc_1082_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1069_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v___x_1068_, v_x_1014_, v_x_1015_);
                v___x_1077_ = 7usize;
                v___x_1078_ = lean_usize_dec_le(v___x_1077_, v_x_1013_);
                if v___x_1078_ == 0 {
                    v___x_1079_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1069_);
                    v___x_1080_ = lean_unsigned_to_nat(4);
                    v___x_1081_ = lean_nat_dec_lt(v___x_1079_, v___x_1080_);
                    lean_dec(v___x_1079_);
                    v___y_1071_ = v___x_1081_;
                    state = 10;
                    continue;
                } else {
                    v___y_1071_ = v___x_1078_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1071_ == 0 {
                    v_ks_1072_ = lean_ctor_get(v_newNode_1069_, 0);
                    lean_inc_ref(v_ks_1072_);
                    v_vs_1073_ = lean_ctor_get(v_newNode_1069_, 1);
                    lean_inc_ref(v_vs_1073_);
                    lean_dec_ref(v_newNode_1069_);
                    v___x_1074_ = lean_unsigned_to_nat(0);
                    v___x_1075_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2);
                    v___x_1076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_x_1013_, v_ks_1072_, v_vs_1073_, v___x_1074_, v___x_1075_);
                    lean_dec_ref(v_vs_1073_);
                    lean_dec_ref(v_ks_1072_);
                    return v___x_1076_;
                } else {
                    return v_newNode_1069_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_depth_1084_: usize,
    mut v_keys_1085_: *mut LeanObject,
    mut v_vals_1086_: *mut LeanObject,
    mut v_i_1087_: *mut LeanObject,
    mut v_entries_1088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    let mut v_k_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1094_: u64 = 0;
    let mut v_h_1095_: usize = 0;
    let mut v___x_1096_: usize = 0;
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: usize = 0;
    let mut v___x_1099_: usize = 0;
    let mut v___x_1100_: usize = 0;
    let mut v_h_1101_: usize = 0;
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: u64 = 0;
    let mut v_hash_1106_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1089_ = lean_array_get_size(v_keys_1085_);
                v___x_1090_ = lean_nat_dec_lt(v_i_1087_, v___x_1089_);
                if v___x_1090_ == 0 {
                    lean_dec(v_i_1087_);
                    return v_entries_1088_;
                } else {
                    v_k_1091_ = lean_array_fget_borrowed(v_keys_1085_, v_i_1087_);
                    v_v_1092_ = lean_array_fget_borrowed(v_vals_1086_, v_i_1087_);
                    if lean_obj_tag(v_k_1091_) == 0 {
                        v___x_1105_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
                        v___y_1094_ = v___x_1105_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_1106_ = lean_ctor_get_uint64(
                            v_k_1091_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v___y_1094_ = v_hash_1106_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_1095_ = lean_uint64_to_usize(v___y_1094_);
                v___x_1096_ = 5usize;
                v___x_1097_ = lean_unsigned_to_nat(1);
                v___x_1098_ = 1usize;
                v___x_1099_ = lean_usize_sub(v_depth_1084_, v___x_1098_);
                v___x_1100_ = lean_usize_mul(v___x_1096_, v___x_1099_);
                v_h_1101_ = lean_usize_shift_right(v_h_1095_, v___x_1100_);
                v___x_1102_ = lean_nat_add(v_i_1087_, v___x_1097_);
                lean_dec(v_i_1087_);
                lean_inc(v_v_1092_);
                lean_inc(v_k_1091_);
                v___x_1103_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_entries_1088_, v_h_1101_, v_depth_1084_, v_k_1091_, v_v_1092_);
                v_i_1087_ = v___x_1102_;
                v_entries_1088_ = v___x_1103_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_depth_1107_: *mut LeanObject,
    mut v_keys_1108_: *mut LeanObject,
    mut v_vals_1109_: *mut LeanObject,
    mut v_i_1110_: *mut LeanObject,
    mut v_entries_1111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1112_: usize = 0;
    let mut v_res_1113_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1112_ = lean_unbox_usize(v_depth_1107_);
    lean_dec(v_depth_1107_);
    v_res_1113_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_depth_boxed_1112_, v_keys_1108_, v_vals_1109_, v_i_1110_, v_entries_1111_);
    lean_dec_ref(v_vals_1109_);
    lean_dec_ref(v_keys_1108_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_1114_: *mut LeanObject,
    mut v_x_1115_: *mut LeanObject,
    mut v_x_1116_: *mut LeanObject,
    mut v_x_1117_: *mut LeanObject,
    mut v_x_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_660__boxed_1119_: usize = 0;
    let mut v_x_661__boxed_1120_: usize = 0;
    let mut v_res_1121_: *mut LeanObject = core::ptr::null_mut();
    v_x_660__boxed_1119_ = lean_unbox_usize(v_x_1115_);
    lean_dec(v_x_1115_);
    v_x_661__boxed_1120_ = lean_unbox_usize(v_x_1116_);
    lean_dec(v_x_1116_);
    v_res_1121_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1114_, v_x_660__boxed_1119_, v_x_661__boxed_1120_, v_x_1117_, v_x_1118_);
    return v_res_1121_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_1122_: *mut LeanObject,
    mut v_x_1123_: *mut LeanObject,
    mut v_x_1124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1126_: u64 = 0;
    let mut v___x_1127_: usize = 0;
    let mut v___x_1128_: usize = 0;
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: u64 = 0;
    let mut v_hash_1131_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1123_) == 0 {
                    v___x_1130_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
                    v___y_1126_ = v___x_1130_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1131_ = lean_ctor_get_uint64(
                        v_x_1123_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1126_ = v_hash_1131_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1127_ = lean_uint64_to_usize(v___y_1126_);
                v___x_1128_ = 1usize;
                v___x_1129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1122_, v___x_1127_, v___x_1128_, v_x_1123_, v_x_1124_);
                return v___x_1129_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__2(
    mut v_msg_1132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    v___x_1133_ = l_Lean_instInhabitedExpr;
    v___x_1134_ = lean_panic_fn_borrowed(v___x_1133_, v_msg_1132_);
    return v___x_1134_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_keys_1135_: *mut LeanObject,
    mut v_vals_1136_: *mut LeanObject,
    mut v_i_1137_: *mut LeanObject,
    mut v_k_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: u8 = 0;
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: u8 = 0;
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1139_ = lean_array_get_size(v_keys_1135_);
                v___x_1140_ = lean_nat_dec_lt(v_i_1137_, v___x_1139_);
                if v___x_1140_ == 0 {
                    lean_dec(v_i_1137_);
                    v___x_1141_ = lean_box(0);
                    return v___x_1141_;
                } else {
                    v_k_x27_1142_ = lean_array_fget_borrowed(v_keys_1135_, v_i_1137_);
                    v___x_1143_ = lean_name_eq(v_k_1138_, v_k_x27_1142_);
                    if v___x_1143_ == 0 {
                        v___x_1144_ = lean_unsigned_to_nat(1);
                        v___x_1145_ = lean_nat_add(v_i_1137_, v___x_1144_);
                        lean_dec(v_i_1137_);
                        v_i_1137_ = v___x_1145_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1147_ = lean_array_fget_borrowed(v_vals_1136_, v_i_1137_);
                        lean_dec(v_i_1137_);
                        lean_inc(v___x_1147_);
                        v___x_1148_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1148_, 0, v___x_1147_);
                        return v___x_1148_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_keys_1149_: *mut LeanObject,
    mut v_vals_1150_: *mut LeanObject,
    mut v_i_1151_: *mut LeanObject,
    mut v_k_1152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1153_: *mut LeanObject = core::ptr::null_mut();
    v_res_1153_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_keys_1149_, v_vals_1150_, v_i_1151_, v_k_1152_);
    lean_dec(v_k_1152_);
    lean_dec_ref(v_vals_1150_);
    lean_dec_ref(v_keys_1149_);
    return v_res_1153_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(
    mut v_x_1154_: *mut LeanObject,
    mut v_x_1155_: usize,
    mut v_x_1156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: usize = 0;
    let mut v___x_1160_: usize = 0;
    let mut v___x_1161_: usize = 0;
    let mut v_j_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: u8 = 0;
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: usize = 0;
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1154_) == 0 {
                    v_es_1157_ = lean_ctor_get(v_x_1154_, 0);
                    v___x_1158_ = lean_box(2);
                    v___x_1159_ = 5usize;
                    v___x_1160_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_1161_ = lean_usize_land(v_x_1155_, v___x_1160_);
                    v_j_1162_ = lean_usize_to_nat(v___x_1161_);
                    v___x_1163_ = lean_array_get_borrowed(v___x_1158_, v_es_1157_, v_j_1162_);
                    lean_dec(v_j_1162_);
                    match lean_obj_tag(v___x_1163_) {
                        0 => {
                            v_key_1164_ = lean_ctor_get(v___x_1163_, 0);
                            v_val_1165_ = lean_ctor_get(v___x_1163_, 1);
                            v___x_1166_ = lean_name_eq(v_x_1156_, v_key_1164_);
                            if v___x_1166_ == 0 {
                                v___x_1167_ = lean_box(0);
                                return v___x_1167_;
                            } else {
                                lean_inc(v_val_1165_);
                                v___x_1168_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_1168_, 0, v_val_1165_);
                                return v___x_1168_;
                            }
                        }
                        1 => {
                            v_node_1169_ = lean_ctor_get(v___x_1163_, 0);
                            v___x_1170_ = lean_usize_shift_right(v_x_1155_, v___x_1159_);
                            v_x_1154_ = v_node_1169_;
                            v_x_1155_ = v___x_1170_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1172_ = lean_box(0);
                            return v___x_1172_;
                        }
                    }
                } else {
                    v_ks_1173_ = lean_ctor_get(v_x_1154_, 0);
                    v_vs_1174_ = lean_ctor_get(v_x_1154_, 1);
                    v___x_1175_ = lean_unsigned_to_nat(0);
                    v___x_1176_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_ks_1173_, v_vs_1174_, v___x_1175_, v_x_1156_);
                    return v___x_1176_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg___boxed(
    mut v_x_1177_: *mut LeanObject,
    mut v_x_1178_: *mut LeanObject,
    mut v_x_1179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_875__boxed_1180_: usize = 0;
    let mut v_res_1181_: *mut LeanObject = core::ptr::null_mut();
    v_x_875__boxed_1180_ = lean_unbox_usize(v_x_1178_);
    lean_dec(v_x_1178_);
    v_res_1181_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_1177_, v_x_875__boxed_1180_, v_x_1179_);
    lean_dec(v_x_1179_);
    lean_dec_ref(v_x_1177_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_x_1182_: *mut LeanObject,
    mut v_x_1183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1185_: u64 = 0;
    let mut v___x_1186_: usize = 0;
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: u64 = 0;
    let mut v_hash_1189_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1183_) == 0 {
                    v___x_1188_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
                    v___y_1185_ = v___x_1188_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1189_ = lean_ctor_get_uint64(
                        v_x_1183_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1185_ = v_hash_1189_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1186_ = lean_uint64_to_usize(v___y_1185_);
                v___x_1187_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_1182_, v___x_1186_, v_x_1183_);
                return v___x_1187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(
    mut v_x_1190_: *mut LeanObject,
    mut v_x_1191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1192_: *mut LeanObject = core::ptr::null_mut();
    v_res_1192_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_1190_, v_x_1191_);
    lean_dec(v_x_1191_);
    lean_dec_ref(v_x_1190_);
    return v_res_1192_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    v___x_1196_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__2;
    v___x_1197_ = lean_unsigned_to_nat(14);
    v___x_1198_ = lean_unsigned_to_nat(177);
    v___x_1199_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__1;
    v___x_1200_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__0;
    v___x_1201_ = l_mkPanicMessageWithDecl(
        v___x_1200_,
        v___x_1199_,
        v___x_1198_,
        v___x_1197_,
        v___x_1196_,
    );
    return v___x_1201_;
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3(
    mut v_newState_1202_: *mut LeanObject,
    mut v_x_1203_: *mut LeanObject,
    mut v_x_1204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v_fst_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1214_: u8 = 0;
    let mut v_snd_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1230_: u8 = 0;
    let mut v_isSharedCheck_1231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1204_) == 0 {
                    return v_x_1203_;
                } else {
                    v_head_1205_ = lean_ctor_get(v_x_1204_, 0);
                    v_tail_1206_ = lean_ctor_get(v_x_1204_, 1);
                    v_isSharedCheck_1231_ = (!lean_is_exclusive(v_x_1204_)) as u8;
                    if v_isSharedCheck_1231_ == 0 {
                        v___x_1208_ = v_x_1204_;
                        v_isShared_1209_ = v_isSharedCheck_1231_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1206_);
                        lean_inc(v_head_1205_);
                        lean_dec(v_x_1204_);
                        v___x_1208_ = lean_box(0);
                        v_isShared_1209_ = v_isSharedCheck_1231_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1210_ = lean_ctor_get(v_x_1203_, 0);
                v_snd_1211_ = lean_ctor_get(v_x_1203_, 1);
                v_isSharedCheck_1230_ = (!lean_is_exclusive(v_x_1203_)) as u8;
                if v_isSharedCheck_1230_ == 0 {
                    v___x_1213_ = v_x_1203_;
                    v_isShared_1214_ = v_isSharedCheck_1230_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1211_);
                    lean_inc(v_fst_1210_);
                    lean_dec(v_x_1203_);
                    v___x_1213_ = lean_box(0);
                    v_isShared_1214_ = v_isSharedCheck_1230_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_1215_ = lean_ctor_get(v_newState_1202_, 1);
                lean_inc(v_head_1205_);
                if v_isShared_1209_ == 0 {
                    lean_ctor_set(v___x_1208_, 1, v_fst_1210_);
                    v___x_1217_ = v___x_1208_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_head_1205_);
                    lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_fst_1210_);
                    v___x_1217_ = v_reuseFailAlloc_1229_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1225_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_1215_, v_head_1205_);
                if lean_obj_tag(v___x_1225_) == 0 {
                    v___x_1226_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___closed__3);
                    v___x_1227_ = l_panic___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__2(v___x_1226_);
                    v___y_1219_ = v___x_1227_;
                    state = 4;
                    continue;
                } else {
                    v_val_1228_ = lean_ctor_get(v___x_1225_, 0);
                    lean_inc(v_val_1228_);
                    lean_dec_ref_known(v___x_1225_, 1);
                    v___y_1219_ = v_val_1228_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1220_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_1211_, v_head_1205_, v___y_1219_);
                if v_isShared_1214_ == 0 {
                    lean_ctor_set(v___x_1213_, 1, v___x_1220_);
                    lean_ctor_set(v___x_1213_, 0, v___x_1217_);
                    v___x_1222_ = v___x_1213_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1217_);
                    lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___x_1220_);
                    v___x_1222_ = v_reuseFailAlloc_1224_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_x_1203_ = v___x_1222_;
                v_x_1204_ = v_tail_1206_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3___boxed(
    mut v_newState_1232_: *mut LeanObject,
    mut v_x_1233_: *mut LeanObject,
    mut v_x_1234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1235_: *mut LeanObject = core::ptr::null_mut();
    v_res_1235_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3(v_newState_1232_, v_x_1233_, v_x_1234_);
    lean_dec_ref(v_newState_1232_);
    return v_res_1235_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__0(
    mut v_oldState_1238_: *mut LeanObject,
    mut v_newState_1239_: *mut LeanObject,
    mut v_x_1240_: *mut LeanObject,
    mut v_s_1241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newEntries_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1242_ = lean_ctor_get(v_newState_1239_, 0);
    v_fst_1243_ = lean_ctor_get(v_oldState_1238_, 0);
    v___x_1244_ = l_List_lengthTR___redArg(v_fst_1242_);
    v___x_1245_ = l_List_lengthTR___redArg(v_fst_1243_);
    v___x_1246_ = lean_nat_sub(v___x_1244_, v___x_1245_);
    lean_dec(v___x_1245_);
    lean_dec(v___x_1244_);
    v___x_1247_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__0___closed__0;
    lean_inc(v_fst_1242_);
    v_newEntries_1248_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(
        lean_box(0),
        v_fst_1242_,
        v_fst_1242_,
        v___x_1246_,
        v___x_1247_,
    );
    v___x_1249_ = l_List_foldl___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__3(v_newState_1239_, v_s_1241_, v_newEntries_1248_);
    lean_dec_ref(v_newState_1239_);
    return v___x_1249_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__0___boxed(
    mut v_oldState_1250_: *mut LeanObject,
    mut v_newState_1251_: *mut LeanObject,
    mut v_x_1252_: *mut LeanObject,
    mut v_s_1253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1254_: *mut LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__0(v_oldState_1250_, v_newState_1251_, v_x_1252_, v_s_1253_);
    lean_dec(v_x_1252_);
    lean_dec_ref(v_oldState_1250_);
    return v_res_1254_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    v___x_1256_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1256_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    v___x_1257_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__1);
    v___x_1258_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1258_, 0, v___x_1257_);
    return v___x_1258_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___x_1259_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__2);
    v___x_1260_ = lean_box(0);
    v___x_1261_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1261_, 0, v___x_1260_);
    lean_ctor_set(v___x_1261_, 1, v___x_1259_);
    return v___x_1261_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1263_: *mut LeanObject = core::ptr::null_mut();
    v___x_1262_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__3);
    v___f_1263_ = lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1263_, 0, v___x_1262_);
    return v___f_1263_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0()
-> *mut LeanObject {
    let mut v___f_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut v_a_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1267_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__4_once), _init_l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__4);
                v___x_1268_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___closed__5;
                v___x_1269_ = lean_box(0);
                v___x_1270_ =
                    l_Lean_registerEnvExtension___redArg(v___f_1267_, v___x_1268_, v___x_1269_);
                if lean_obj_tag(v___x_1270_) == 0 {
                    v_a_1271_ = lean_ctor_get(v___x_1270_, 0);
                    v_isSharedCheck_1278_ = (!lean_is_exclusive(v___x_1270_)) as u8;
                    if v_isSharedCheck_1278_ == 0 {
                        v___x_1273_ = v___x_1270_;
                        v_isShared_1274_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1271_);
                        lean_dec(v___x_1270_);
                        v___x_1273_ = lean_box(0);
                        v_isShared_1274_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1279_ = lean_ctor_get(v___x_1270_, 0);
                    v_isSharedCheck_1286_ = (!lean_is_exclusive(v___x_1270_)) as u8;
                    if v_isSharedCheck_1286_ == 0 {
                        v___x_1281_ = v___x_1270_;
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1279_);
                        lean_dec(v___x_1270_);
                        v___x_1281_ = lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1274_ == 0 {
                    v___x_1276_ = v___x_1273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
                    v___x_1276_ = v_reuseFailAlloc_1277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1276_;
            }
            3 => {
                if v_isShared_1282_ == 0 {
                    v___x_1284_ = v___x_1281_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
                    v___x_1284_ = v_reuseFailAlloc_1285_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0___boxed(
    mut v_a_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1288_: *mut LeanObject = core::ptr::null_mut();
    v_res_1288_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0();
    return v_res_1288_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    v___x_1290_ = l_Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0();
    return v___x_1290_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2____boxed(
    mut v_a_1291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1292_: *mut LeanObject = core::ptr::null_mut();
    v_res_1292_ = l___private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2_();
    return v_res_1292_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_1293_: *mut LeanObject,
    mut v_x_1294_: *mut LeanObject,
    mut v_x_1295_: *mut LeanObject,
    mut v_x_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    v___x_1297_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1294_, v_x_1295_, v_x_1296_);
    return v___x_1297_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_1298_: *mut LeanObject,
    mut v_x_1299_: *mut LeanObject,
    mut v_x_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    v___x_1301_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1___redArg(v_x_1299_, v_x_1300_);
    return v___x_1301_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_00_u03b2_1302_: *mut LeanObject,
    mut v_x_1303_: *mut LeanObject,
    mut v_x_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1305_: *mut LeanObject = core::ptr::null_mut();
    v_res_1305_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b2_1302_, v_x_1303_, v_x_1304_);
    lean_dec(v_x_1304_);
    lean_dec_ref(v_x_1303_);
    return v_res_1305_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b2_1306_: *mut LeanObject,
    mut v_x_1307_: *mut LeanObject,
    mut v_x_1308_: usize,
    mut v_x_1309_: usize,
    mut v_x_1310_: *mut LeanObject,
    mut v_x_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_1307_, v_x_1308_, v_x_1309_, v_x_1310_, v_x_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1313_: *mut LeanObject,
    mut v_x_1314_: *mut LeanObject,
    mut v_x_1315_: *mut LeanObject,
    mut v_x_1316_: *mut LeanObject,
    mut v_x_1317_: *mut LeanObject,
    mut v_x_1318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1140__boxed_1319_: usize = 0;
    let mut v_x_1141__boxed_1320_: usize = 0;
    let mut v_res_1321_: *mut LeanObject = core::ptr::null_mut();
    v_x_1140__boxed_1319_ = lean_unbox_usize(v_x_1315_);
    lean_dec(v_x_1315_);
    v_x_1141__boxed_1320_ = lean_unbox_usize(v_x_1316_);
    lean_dec(v_x_1316_);
    v_res_1321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_1313_, v_x_1314_, v_x_1140__boxed_1319_, v_x_1141__boxed_1320_, v_x_1317_, v_x_1318_);
    return v_res_1321_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3(
    mut v_00_u03b2_1322_: *mut LeanObject,
    mut v_x_1323_: *mut LeanObject,
    mut v_x_1324_: usize,
    mut v_x_1325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1326_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3___redArg(v_x_1323_, v_x_1324_, v_x_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_1327_: *mut LeanObject,
    mut v_x_1328_: *mut LeanObject,
    mut v_x_1329_: *mut LeanObject,
    mut v_x_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1157__boxed_1331_: usize = 0;
    let mut v_res_1332_: *mut LeanObject = core::ptr::null_mut();
    v_x_1157__boxed_1331_ = lean_unbox_usize(v_x_1329_);
    lean_dec(v_x_1329_);
    v_res_1332_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_00_u03b2_1327_, v_x_1328_, v_x_1157__boxed_1331_, v_x_1330_);
    lean_dec(v_x_1330_);
    lean_dec_ref(v_x_1328_);
    return v_res_1332_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_1333_: *mut LeanObject,
    mut v_n_1334_: *mut LeanObject,
    mut v_k_1335_: *mut LeanObject,
    mut v_v_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    v___x_1337_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_n_1334_, v_k_1335_, v_v_1336_);
    return v___x_1337_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_1338_: *mut LeanObject,
    mut v_depth_1339_: usize,
    mut v_keys_1340_: *mut LeanObject,
    mut v_vals_1341_: *mut LeanObject,
    mut v_heq_1342_: *mut LeanObject,
    mut v_i_1343_: *mut LeanObject,
    mut v_entries_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    v___x_1345_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_depth_1339_, v_keys_1340_, v_vals_1341_, v_i_1343_, v_entries_1344_);
    return v___x_1345_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_1346_: *mut LeanObject,
    mut v_depth_1347_: *mut LeanObject,
    mut v_keys_1348_: *mut LeanObject,
    mut v_vals_1349_: *mut LeanObject,
    mut v_heq_1350_: *mut LeanObject,
    mut v_i_1351_: *mut LeanObject,
    mut v_entries_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1353_: usize = 0;
    let mut v_res_1354_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1353_ = lean_unbox_usize(v_depth_1347_);
    lean_dec(v_depth_1347_);
    v_res_1354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1346_, v_depth_boxed_1353_, v_keys_1348_, v_vals_1349_, v_heq_1350_, v_i_1351_, v_entries_1352_);
    lean_dec_ref(v_vals_1349_);
    lean_dec_ref(v_keys_1348_);
    return v_res_1354_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b2_1355_: *mut LeanObject,
    mut v_keys_1356_: *mut LeanObject,
    mut v_vals_1357_: *mut LeanObject,
    mut v_heq_1358_: *mut LeanObject,
    mut v_i_1359_: *mut LeanObject,
    mut v_k_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    v___x_1361_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___redArg(v_keys_1356_, v_vals_1357_, v_i_1359_, v_k_1360_);
    return v___x_1361_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_1362_: *mut LeanObject,
    mut v_keys_1363_: *mut LeanObject,
    mut v_vals_1364_: *mut LeanObject,
    mut v_heq_1365_: *mut LeanObject,
    mut v_i_1366_: *mut LeanObject,
    mut v_k_1367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1368_: *mut LeanObject = core::ptr::null_mut();
    v_res_1368_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1_spec__3_spec__7(v_00_u03b2_1362_, v_keys_1363_, v_vals_1364_, v_heq_1365_, v_i_1366_, v_k_1367_);
    lean_dec(v_k_1367_);
    lean_dec_ref(v_vals_1364_);
    lean_dec_ref(v_keys_1363_);
    return v_res_1368_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_1369_: *mut LeanObject,
    mut v_x_1370_: *mut LeanObject,
    mut v_x_1371_: *mut LeanObject,
    mut v_x_1372_: *mut LeanObject,
    mut v_x_1373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    v___x_1374_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__6___redArg(v_x_1370_, v_x_1371_, v_x_1372_, v_x_1373_);
    return v___x_1374_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___lam__0(
    mut v_a_1375_: *mut LeanObject,
    mut v_b_1376_: *mut LeanObject,
    mut v_x_1377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1382_: u8 = 0;
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1378_ = lean_ctor_get(v_x_1377_, 0);
                v_snd_1379_ = lean_ctor_get(v_x_1377_, 1);
                v_isSharedCheck_1388_ = (!lean_is_exclusive(v_x_1377_)) as u8;
                if v_isSharedCheck_1388_ == 0 {
                    v___x_1381_ = v_x_1377_;
                    v_isShared_1382_ = v_isSharedCheck_1388_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1379_);
                    lean_inc(v_fst_1378_);
                    lean_dec(v_x_1377_);
                    v___x_1381_ = lean_box(0);
                    v_isShared_1382_ = v_isSharedCheck_1388_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_a_1375_);
                v___x_1383_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1383_, 0, v_a_1375_);
                lean_ctor_set(v___x_1383_, 1, v_fst_1378_);
                v___x_1384_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__0___redArg(v_snd_1379_, v_a_1375_, v_b_1376_);
                if v_isShared_1382_ == 0 {
                    lean_ctor_set(v___x_1381_, 1, v___x_1384_);
                    lean_ctor_set(v___x_1381_, 0, v___x_1383_);
                    v___x_1386_ = v___x_1381_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1383_);
                    lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___x_1384_);
                    v___x_1386_ = v_reuseFailAlloc_1387_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    v___x_1389_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1389_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    v___x_1390_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__0_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__0);
    v___x_1391_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1391_, 0, v___x_1390_);
    return v___x_1391_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    v___x_1392_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__1_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__1);
    v___x_1393_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1393_, 0, v___x_1392_);
    lean_ctor_set(v___x_1393_, 1, v___x_1392_);
    return v___x_1393_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(
    mut v_ext_1394_: *mut LeanObject,
    mut v_a_1395_: *mut LeanObject,
    mut v_b_1396_: *mut LeanObject,
    mut v_a_1397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v_asyncMode_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut v_unused_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1399_ = lean_st_ref_take(v_a_1397_);
                v_env_1400_ = lean_ctor_get(v___x_1399_, 0);
                v_nextMacroScope_1401_ = lean_ctor_get(v___x_1399_, 1);
                v_ngen_1402_ = lean_ctor_get(v___x_1399_, 2);
                v_auxDeclNGen_1403_ = lean_ctor_get(v___x_1399_, 3);
                v_traceState_1404_ = lean_ctor_get(v___x_1399_, 4);
                v_messages_1405_ = lean_ctor_get(v___x_1399_, 6);
                v_infoState_1406_ = lean_ctor_get(v___x_1399_, 7);
                v_snapshotTasks_1407_ = lean_ctor_get(v___x_1399_, 8);
                v_isSharedCheck_1422_ = (!lean_is_exclusive(v___x_1399_)) as u8;
                if v_isSharedCheck_1422_ == 0 {
                    v_unused_1423_ = lean_ctor_get(v___x_1399_, 5);
                    lean_dec(v_unused_1423_);
                    v___x_1409_ = v___x_1399_;
                    v_isShared_1410_ = v_isSharedCheck_1422_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1407_);
                    lean_inc(v_infoState_1406_);
                    lean_inc(v_messages_1405_);
                    lean_inc(v_traceState_1404_);
                    lean_inc(v_auxDeclNGen_1403_);
                    lean_inc(v_ngen_1402_);
                    lean_inc(v_nextMacroScope_1401_);
                    lean_inc(v_env_1400_);
                    lean_dec(v___x_1399_);
                    v___x_1409_ = lean_box(0);
                    v_isShared_1410_ = v_isSharedCheck_1422_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_asyncMode_1411_ = lean_ctor_get(v_ext_1394_, 2);
                lean_inc(v_asyncMode_1411_);
                v___f_1412_ = lean_alloc_closure(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_1412_, 0, v_a_1395_);
                lean_closure_set(v___f_1412_, 1, v_b_1396_);
                v___x_1413_ = lean_box(0);
                v___x_1414_ = l_Lean_EnvExtension_modifyState___redArg(
                    v_ext_1394_,
                    v_env_1400_,
                    v___f_1412_,
                    v_asyncMode_1411_,
                    v___x_1413_,
                );
                lean_dec(v_asyncMode_1411_);
                v___x_1415_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___closed__2);
                if v_isShared_1410_ == 0 {
                    lean_ctor_set(v___x_1409_, 5, v___x_1415_);
                    lean_ctor_set(v___x_1409_, 0, v___x_1414_);
                    v___x_1417_ = v___x_1409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1414_);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_nextMacroScope_1401_);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_ngen_1402_);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_auxDeclNGen_1403_);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_traceState_1404_);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 5, v___x_1415_);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 6, v_messages_1405_);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 7, v_infoState_1406_);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 8, v_snapshotTasks_1407_);
                    v___x_1417_ = v_reuseFailAlloc_1421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1418_ = lean_st_ref_set(v_a_1397_, v___x_1417_);
                v___x_1419_ = lean_box(0);
                v___x_1420_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1420_, 0, v___x_1419_);
                return v___x_1420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg___boxed(
    mut v_ext_1424_: *mut LeanObject,
    mut v_a_1425_: *mut LeanObject,
    mut v_b_1426_: *mut LeanObject,
    mut v_a_1427_: *mut LeanObject,
    mut v_a_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1429_: *mut LeanObject = core::ptr::null_mut();
    v_res_1429_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(v_ext_1424_, v_a_1425_, v_b_1426_, v_a_1427_);
    lean_dec(v_a_1427_);
    return v_res_1429_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__1;
    v___x_1433_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__0;
    v___x_1434_ =
        l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), v___x_1433_, v___x_1432_);
    return v___x_1434_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    v___x_1435_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__2_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__2);
    v___x_1436_ = lean_box(0);
    v___x_1437_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1437_, 0, v___x_1436_);
    lean_ctor_set(v___x_1437_, 1, v___x_1435_);
    return v___x_1437_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg(
    mut v_ext_1438_: *mut LeanObject,
    mut v_a_1439_: *mut LeanObject,
    mut v_a_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = lean_st_ref_get(v_a_1440_);
    v_env_1443_ = lean_ctor_get(v___x_1442_, 0);
    lean_inc_ref(v_env_1443_);
    lean_dec(v___x_1442_);
    v_asyncMode_1444_ = lean_ctor_get(v_ext_1438_, 2);
    v___x_1445_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__3_once), _init_l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___closed__3);
    v___x_1446_ = lean_box(0);
    v___x_1447_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_1445_,
        v_ext_1438_,
        v_env_1443_,
        v_asyncMode_1444_,
        v___x_1446_,
    );
    v_snd_1448_ = lean_ctor_get(v___x_1447_, 1);
    lean_inc(v_snd_1448_);
    lean_dec(v___x_1447_);
    v___x_1449_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_CacheExtension_register___at___00__private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2__spec__0_spec__1___redArg(v_snd_1448_, v_a_1439_);
    lean_dec(v_snd_1448_);
    v___x_1450_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1450_, 0, v___x_1449_);
    return v___x_1450_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg___boxed(
    mut v_ext_1451_: *mut LeanObject,
    mut v_a_1452_: *mut LeanObject,
    mut v_a_1453_: *mut LeanObject,
    mut v_a_1454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1455_: *mut LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg(v_ext_1451_, v_a_1452_, v_a_1453_);
    lean_dec(v_a_1453_);
    lean_dec(v_a_1452_);
    lean_dec_ref(v_ext_1451_);
    return v_res_1455_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0()
-> *mut LeanObject {
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    v___x_1456_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1456_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1()
-> *mut LeanObject {
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__0);
    v___x_1458_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1458_, 0, v___x_1457_);
    return v___x_1458_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2()
-> *mut LeanObject {
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    v___x_1459_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1);
    v___x_1460_ = lean_unsigned_to_nat(0);
    v___x_1461_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1461_, 0, v___x_1460_);
    lean_ctor_set(v___x_1461_, 1, v___x_1460_);
    lean_ctor_set(v___x_1461_, 2, v___x_1460_);
    lean_ctor_set(v___x_1461_, 3, v___x_1460_);
    lean_ctor_set(v___x_1461_, 4, v___x_1459_);
    lean_ctor_set(v___x_1461_, 5, v___x_1459_);
    lean_ctor_set(v___x_1461_, 6, v___x_1459_);
    lean_ctor_set(v___x_1461_, 7, v___x_1459_);
    lean_ctor_set(v___x_1461_, 8, v___x_1459_);
    lean_ctor_set(v___x_1461_, 9, v___x_1459_);
    return v___x_1461_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3()
-> *mut LeanObject {
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    v___x_1462_ = lean_unsigned_to_nat(32);
    v___x_1463_ = lean_mk_empty_array_with_capacity(v___x_1462_);
    v___x_1464_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1464_, 0, v___x_1463_);
    return v___x_1464_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4()
-> *mut LeanObject {
    let mut v___x_1465_: usize = 0;
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    v___x_1465_ = 5usize;
    v___x_1466_ = lean_unsigned_to_nat(0);
    v___x_1467_ = lean_unsigned_to_nat(32);
    v___x_1468_ = lean_mk_empty_array_with_capacity(v___x_1467_);
    v___x_1469_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__3);
    v___x_1470_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1470_, 0, v___x_1469_);
    lean_ctor_set(v___x_1470_, 1, v___x_1468_);
    lean_ctor_set(v___x_1470_, 2, v___x_1466_);
    lean_ctor_set(v___x_1470_, 3, v___x_1466_);
    lean_ctor_set_usize(v___x_1470_, 4, v___x_1465_);
    return v___x_1470_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5()
-> *mut LeanObject {
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    v___x_1471_ = lean_box(1);
    v___x_1472_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4);
    v___x_1473_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__1);
    v___x_1474_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1474_, 0, v___x_1473_);
    lean_ctor_set(v___x_1474_, 1, v___x_1472_);
    lean_ctor_set(v___x_1474_, 2, v___x_1471_);
    return v___x_1474_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9(
    mut v_msgData_1475_: *mut LeanObject,
    mut v___y_1476_: *mut LeanObject,
    mut v___y_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    v___x_1479_ = lean_st_ref_get(v___y_1477_);
    v_env_1480_ = lean_ctor_get(v___x_1479_, 0);
    lean_inc_ref(v_env_1480_);
    lean_dec(v___x_1479_);
    v_options_1481_ = lean_ctor_get(v___y_1476_, 2);
    v___x_1482_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2);
    v___x_1483_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5);
    lean_inc_ref(v_options_1481_);
    v___x_1484_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1484_, 0, v_env_1480_);
    lean_ctor_set(v___x_1484_, 1, v___x_1482_);
    lean_ctor_set(v___x_1484_, 2, v___x_1483_);
    lean_ctor_set(v___x_1484_, 3, v_options_1481_);
    v___x_1485_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1485_, 0, v___x_1484_);
    lean_ctor_set(v___x_1485_, 1, v_msgData_1475_);
    v___x_1486_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1486_, 0, v___x_1485_);
    return v___x_1486_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___boxed(
    mut v_msgData_1487_: *mut LeanObject,
    mut v___y_1488_: *mut LeanObject,
    mut v___y_1489_: *mut LeanObject,
    mut v___y_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1491_: *mut LeanObject = core::ptr::null_mut();
    v_res_1491_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9(v_msgData_1487_, v___y_1488_, v___y_1489_);
    lean_dec(v___y_1489_);
    lean_dec_ref(v___y_1488_);
    return v_res_1491_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(
    mut v_msg_1492_: *mut LeanObject,
    mut v___y_1493_: *mut LeanObject,
    mut v___y_1494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1501_: u8 = 0;
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1496_ = lean_ctor_get(v___y_1493_, 5);
                v___x_1497_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9(v_msg_1492_, v___y_1493_, v___y_1494_);
                v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
                v_isSharedCheck_1506_ = (!lean_is_exclusive(v___x_1497_)) as u8;
                if v_isSharedCheck_1506_ == 0 {
                    v___x_1500_ = v___x_1497_;
                    v_isShared_1501_ = v_isSharedCheck_1506_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1498_);
                    lean_dec(v___x_1497_);
                    v___x_1500_ = lean_box(0);
                    v_isShared_1501_ = v_isSharedCheck_1506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1496_);
                v___x_1502_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1502_, 0, v_ref_1496_);
                lean_ctor_set(v___x_1502_, 1, v_a_1498_);
                if v_isShared_1501_ == 0 {
                    lean_ctor_set_tag(v___x_1500_, 1);
                    lean_ctor_set(v___x_1500_, 0, v___x_1502_);
                    v___x_1504_ = v___x_1500_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
                    v___x_1504_ = v_reuseFailAlloc_1505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_msg_1507_: *mut LeanObject,
    mut v___y_1508_: *mut LeanObject,
    mut v___y_1509_: *mut LeanObject,
    mut v___y_1510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1511_: *mut LeanObject = core::ptr::null_mut();
    v_res_1511_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1507_, v___y_1508_, v___y_1509_);
    lean_dec(v___y_1509_);
    lean_dec_ref(v___y_1508_);
    return v_res_1511_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_1512_: *mut LeanObject,
    mut v_msg_1513_: *mut LeanObject,
    mut v___y_1514_: *mut LeanObject,
    mut v___y_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1529_: u8 = 0;
    let mut v_cancelTk_x3f_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1531_: u8 = 0;
    let mut v_inheritedTraceOptions_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1517_ = lean_ctor_get(v___y_1514_, 0);
    v_fileMap_1518_ = lean_ctor_get(v___y_1514_, 1);
    v_options_1519_ = lean_ctor_get(v___y_1514_, 2);
    v_currRecDepth_1520_ = lean_ctor_get(v___y_1514_, 3);
    v_maxRecDepth_1521_ = lean_ctor_get(v___y_1514_, 4);
    v_ref_1522_ = lean_ctor_get(v___y_1514_, 5);
    v_currNamespace_1523_ = lean_ctor_get(v___y_1514_, 6);
    v_openDecls_1524_ = lean_ctor_get(v___y_1514_, 7);
    v_initHeartbeats_1525_ = lean_ctor_get(v___y_1514_, 8);
    v_maxHeartbeats_1526_ = lean_ctor_get(v___y_1514_, 9);
    v_quotContext_1527_ = lean_ctor_get(v___y_1514_, 10);
    v_currMacroScope_1528_ = lean_ctor_get(v___y_1514_, 11);
    v_diag_1529_ = lean_ctor_get_uint8(
        v___y_1514_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1530_ = lean_ctor_get(v___y_1514_, 12);
    v_suppressElabErrors_1531_ = lean_ctor_get_uint8(
        v___y_1514_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1532_ = lean_ctor_get(v___y_1514_, 13);
    v_ref_1533_ = l_Lean_replaceRef(v_ref_1512_, v_ref_1522_);
    lean_inc_ref(v_inheritedTraceOptions_1532_);
    lean_inc(v_cancelTk_x3f_1530_);
    lean_inc(v_currMacroScope_1528_);
    lean_inc(v_quotContext_1527_);
    lean_inc(v_maxHeartbeats_1526_);
    lean_inc(v_initHeartbeats_1525_);
    lean_inc(v_openDecls_1524_);
    lean_inc(v_currNamespace_1523_);
    lean_inc(v_maxRecDepth_1521_);
    lean_inc(v_currRecDepth_1520_);
    lean_inc_ref(v_options_1519_);
    lean_inc_ref(v_fileMap_1518_);
    lean_inc_ref(v_fileName_1517_);
    v___x_1534_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1534_, 0, v_fileName_1517_);
    lean_ctor_set(v___x_1534_, 1, v_fileMap_1518_);
    lean_ctor_set(v___x_1534_, 2, v_options_1519_);
    lean_ctor_set(v___x_1534_, 3, v_currRecDepth_1520_);
    lean_ctor_set(v___x_1534_, 4, v_maxRecDepth_1521_);
    lean_ctor_set(v___x_1534_, 5, v_ref_1533_);
    lean_ctor_set(v___x_1534_, 6, v_currNamespace_1523_);
    lean_ctor_set(v___x_1534_, 7, v_openDecls_1524_);
    lean_ctor_set(v___x_1534_, 8, v_initHeartbeats_1525_);
    lean_ctor_set(v___x_1534_, 9, v_maxHeartbeats_1526_);
    lean_ctor_set(v___x_1534_, 10, v_quotContext_1527_);
    lean_ctor_set(v___x_1534_, 11, v_currMacroScope_1528_);
    lean_ctor_set(v___x_1534_, 12, v_cancelTk_x3f_1530_);
    lean_ctor_set(v___x_1534_, 13, v_inheritedTraceOptions_1532_);
    lean_ctor_set_uint8(
        v___x_1534_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1529_,
    );
    lean_ctor_set_uint8(
        v___x_1534_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1531_,
    );
    v___x_1535_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1513_, v___x_1534_, v___y_1515_);
    lean_dec_ref_known(v___x_1534_, 14);
    return v___x_1535_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_1536_: *mut LeanObject,
    mut v_msg_1537_: *mut LeanObject,
    mut v___y_1538_: *mut LeanObject,
    mut v___y_1539_: *mut LeanObject,
    mut v___y_1540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1541_: *mut LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1536_, v_msg_1537_, v___y_1538_, v___y_1539_);
    lean_dec(v___y_1539_);
    lean_dec_ref(v___y_1538_);
    lean_dec(v_ref_1536_);
    return v_res_1541_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    v___x_1543_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
    v___x_1544_ = l_Lean_stringToMessageData(v___x_1543_);
    return v___x_1544_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
    v___x_1547_ = l_Lean_stringToMessageData(v___x_1546_);
    return v___x_1547_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    v___x_1549_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
    v___x_1550_ = l_Lean_stringToMessageData(v___x_1549_);
    return v___x_1550_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    v___x_1552_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_1553_ = l_Lean_stringToMessageData(v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    v___x_1555_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_1556_ = l_Lean_stringToMessageData(v___x_1555_);
    return v___x_1556_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    v___x_1558_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_1559_ = l_Lean_stringToMessageData(v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    v___x_1561_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_1562_ = l_Lean_stringToMessageData(v___x_1561_);
    return v___x_1562_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_1563_: *mut LeanObject,
    mut v_declHint_1564_: *mut LeanObject,
    mut v___y_1565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v_isExporting_1570_: u8 = 0;
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: u8 = 0;
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1592_: u8 = 0;
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: u8 = 0;
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1567_ = lean_st_ref_get(v___y_1565_);
                v_env_1568_ = lean_ctor_get(v___x_1567_, 0);
                lean_inc_ref(v_env_1568_);
                lean_dec(v___x_1567_);
                v___x_1569_ = l_Lean_Name_isAnonymous(v_declHint_1564_);
                if v___x_1569_ == 0 {
                    v_isExporting_1570_ = lean_ctor_get_uint8(
                        v_env_1568_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1570_ == 0 {
                        lean_dec_ref(v_env_1568_);
                        lean_dec(v_declHint_1564_);
                        v___x_1571_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1571_, 0, v_msg_1563_);
                        return v___x_1571_;
                    } else {
                        lean_inc_ref(v_env_1568_);
                        v___x_1572_ = l_Lean_Environment_setExporting(v_env_1568_, v___x_1569_);
                        lean_inc(v_declHint_1564_);
                        lean_inc_ref(v___x_1572_);
                        v___x_1573_ = l_Lean_Environment_contains(
                            v___x_1572_,
                            v_declHint_1564_,
                            v_isExporting_1570_,
                        );
                        if v___x_1573_ == 0 {
                            lean_dec_ref(v___x_1572_);
                            lean_dec_ref(v_env_1568_);
                            lean_dec(v_declHint_1564_);
                            v___x_1574_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1574_, 0, v_msg_1563_);
                            return v___x_1574_;
                        } else {
                            v___x_1575_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__2);
                            v___x_1576_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__5);
                            v___x_1577_ = l_Lean_Options_empty;
                            v___x_1578_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1578_, 0, v___x_1572_);
                            lean_ctor_set(v___x_1578_, 1, v___x_1575_);
                            lean_ctor_set(v___x_1578_, 2, v___x_1576_);
                            lean_ctor_set(v___x_1578_, 3, v___x_1577_);
                            lean_inc(v_declHint_1564_);
                            v___x_1579_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1564_, v___x_1569_);
                            v_c_1580_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1580_, 0, v___x_1578_);
                            lean_ctor_set(v_c_1580_, 1, v___x_1579_);
                            v___x_1581_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1568_,
                                v_declHint_1564_,
                            );
                            if lean_obj_tag(v___x_1581_) == 0 {
                                lean_dec_ref(v_env_1568_);
                                lean_dec(v_declHint_1564_);
                                v___x_1582_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                                v___x_1583_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1583_, 0, v___x_1582_);
                                lean_ctor_set(v___x_1583_, 1, v_c_1580_);
                                v___x_1584_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
                                v___x_1585_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1585_, 0, v___x_1583_);
                                lean_ctor_set(v___x_1585_, 1, v___x_1584_);
                                v___x_1586_ = l_Lean_MessageData_note(v___x_1585_);
                                v___x_1587_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1587_, 0, v_msg_1563_);
                                lean_ctor_set(v___x_1587_, 1, v___x_1586_);
                                v___x_1588_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1588_, 0, v___x_1587_);
                                return v___x_1588_;
                            } else {
                                v_val_1589_ = lean_ctor_get(v___x_1581_, 0);
                                v_isSharedCheck_1624_ = (!lean_is_exclusive(v___x_1581_)) as u8;
                                if v_isSharedCheck_1624_ == 0 {
                                    v___x_1591_ = v___x_1581_;
                                    v_isShared_1592_ = v_isSharedCheck_1624_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1589_);
                                    lean_dec(v___x_1581_);
                                    v___x_1591_ = lean_box(0);
                                    v_isShared_1592_ = v_isSharedCheck_1624_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1568_);
                    lean_dec(v_declHint_1564_);
                    v___x_1625_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1625_, 0, v_msg_1563_);
                    return v___x_1625_;
                }
            }
            1 => {
                v___x_1593_ = lean_box(0);
                v___x_1594_ = l_Lean_Environment_header(v_env_1568_);
                lean_dec_ref(v_env_1568_);
                v___x_1595_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1594_);
                v_mod_1596_ = lean_array_get(v___x_1593_, v___x_1595_, v_val_1589_);
                lean_dec(v_val_1589_);
                lean_dec_ref(v___x_1595_);
                v___x_1597_ = l_Lean_isPrivateName(v_declHint_1564_);
                lean_dec(v_declHint_1564_);
                if v___x_1597_ == 0 {
                    v___x_1598_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                    v___x_1599_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1599_, 0, v___x_1598_);
                    lean_ctor_set(v___x_1599_, 1, v_c_1580_);
                    v___x_1600_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_1601_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1601_, 0, v___x_1599_);
                    lean_ctor_set(v___x_1601_, 1, v___x_1600_);
                    v___x_1602_ = l_Lean_MessageData_ofName(v_mod_1596_);
                    v___x_1603_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1603_, 0, v___x_1601_);
                    lean_ctor_set(v___x_1603_, 1, v___x_1602_);
                    v___x_1604_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                    v___x_1605_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1605_, 0, v___x_1603_);
                    lean_ctor_set(v___x_1605_, 1, v___x_1604_);
                    v___x_1606_ = l_Lean_MessageData_note(v___x_1605_);
                    v___x_1607_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1607_, 0, v_msg_1563_);
                    lean_ctor_set(v___x_1607_, 1, v___x_1606_);
                    if v_isShared_1592_ == 0 {
                        lean_ctor_set_tag(v___x_1591_, 0);
                        lean_ctor_set(v___x_1591_, 0, v___x_1607_);
                        v___x_1609_ = v___x_1591_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
                        v___x_1609_ = v_reuseFailAlloc_1610_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1611_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                    v___x_1612_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1612_, 0, v___x_1611_);
                    lean_ctor_set(v___x_1612_, 1, v_c_1580_);
                    v___x_1613_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_1614_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1614_, 0, v___x_1612_);
                    lean_ctor_set(v___x_1614_, 1, v___x_1613_);
                    v___x_1615_ = l_Lean_MessageData_ofName(v_mod_1596_);
                    v___x_1616_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1616_, 0, v___x_1614_);
                    lean_ctor_set(v___x_1616_, 1, v___x_1615_);
                    v___x_1617_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_1618_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1618_, 0, v___x_1616_);
                    lean_ctor_set(v___x_1618_, 1, v___x_1617_);
                    v___x_1619_ = l_Lean_MessageData_note(v___x_1618_);
                    v___x_1620_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1620_, 0, v_msg_1563_);
                    lean_ctor_set(v___x_1620_, 1, v___x_1619_);
                    if v_isShared_1592_ == 0 {
                        lean_ctor_set_tag(v___x_1591_, 0);
                        lean_ctor_set(v___x_1591_, 0, v___x_1620_);
                        v___x_1622_ = v___x_1591_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
                        v___x_1622_ = v_reuseFailAlloc_1623_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1609_;
            }
            3 => {
                return v___x_1622_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msg_1626_: *mut LeanObject,
    mut v_declHint_1627_: *mut LeanObject,
    mut v___y_1628_: *mut LeanObject,
    mut v___y_1629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1630_: *mut LeanObject = core::ptr::null_mut();
    v_res_1630_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1626_, v_declHint_1627_, v___y_1628_);
    lean_dec(v___y_1628_);
    return v_res_1630_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_1631_: *mut LeanObject,
    mut v_declHint_1632_: *mut LeanObject,
    mut v___y_1633_: *mut LeanObject,
    mut v___y_1634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1640_: u8 = 0;
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1636_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1631_, v_declHint_1632_, v___y_1634_);
                v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
                v_isSharedCheck_1646_ = (!lean_is_exclusive(v___x_1636_)) as u8;
                if v_isSharedCheck_1646_ == 0 {
                    v___x_1639_ = v___x_1636_;
                    v_isShared_1640_ = v_isSharedCheck_1646_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1637_);
                    lean_dec(v___x_1636_);
                    v___x_1639_ = lean_box(0);
                    v_isShared_1640_ = v_isSharedCheck_1646_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1641_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1642_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1642_, 0, v___x_1641_);
                lean_ctor_set(v___x_1642_, 1, v_a_1637_);
                if v_isShared_1640_ == 0 {
                    lean_ctor_set(v___x_1639_, 0, v___x_1642_);
                    v___x_1644_ = v___x_1639_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
                    v___x_1644_ = v_reuseFailAlloc_1645_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v_msg_1647_: *mut LeanObject,
    mut v_declHint_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
    mut v___y_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1652_: *mut LeanObject = core::ptr::null_mut();
    v_res_1652_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1647_, v_declHint_1648_, v___y_1649_, v___y_1650_);
    lean_dec(v___y_1650_);
    lean_dec_ref(v___y_1649_);
    return v_res_1652_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_1653_: *mut LeanObject,
    mut v_msg_1654_: *mut LeanObject,
    mut v_declHint_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1654_, v_declHint_1655_, v___y_1656_, v___y_1657_);
    v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
    lean_inc(v_a_1660_);
    lean_dec_ref(v___x_1659_);
    v___x_1661_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1653_, v_a_1660_, v___y_1656_, v___y_1657_);
    return v___x_1661_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_1662_: *mut LeanObject,
    mut v_msg_1663_: *mut LeanObject,
    mut v_declHint_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1668_: *mut LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1662_, v_msg_1663_, v_declHint_1664_, v___y_1665_, v___y_1666_);
    lean_dec(v___y_1666_);
    lean_dec_ref(v___y_1665_);
    lean_dec(v_ref_1662_);
    return v_res_1668_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    v___x_1670_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1671_ = l_Lean_stringToMessageData(v___x_1670_);
    return v___x_1671_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    v___x_1673_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1674_ = l_Lean_stringToMessageData(v___x_1673_);
    return v___x_1674_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1675_: *mut LeanObject,
    mut v_constName_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: u8 = 0;
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    v___x_1680_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1681_ = 0;
    lean_inc(v_constName_1676_);
    v___x_1682_ = l_Lean_MessageData_ofConstName(v_constName_1676_, v___x_1681_);
    v___x_1683_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1683_, 0, v___x_1680_);
    lean_ctor_set(v___x_1683_, 1, v___x_1682_);
    v___x_1684_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1685_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1685_, 0, v___x_1683_);
    lean_ctor_set(v___x_1685_, 1, v___x_1684_);
    v___x_1686_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1675_, v___x_1685_, v_constName_1676_, v___y_1677_, v___y_1678_);
    return v___x_1686_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1687_: *mut LeanObject,
    mut v_constName_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1692_: *mut LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg(v_ref_1687_, v_constName_1688_, v___y_1689_, v___y_1690_);
    lean_dec(v___y_1690_);
    lean_dec_ref(v___y_1689_);
    lean_dec(v_ref_1687_);
    return v_res_1692_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0___redArg(
    mut v_constName_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1697_ = lean_ctor_get(v___y_1694_, 5);
    v___x_1698_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg(v_ref_1697_, v_constName_1693_, v___y_1694_, v___y_1695_);
    return v___x_1698_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0___redArg___boxed(
    mut v_constName_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1703_: *mut LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0___redArg(v_constName_1699_, v___y_1700_, v___y_1701_);
    lean_dec(v___y_1701_);
    lean_dec_ref(v___y_1700_);
    return v_res_1703_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0(
    mut v_constName_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: u8 = 0;
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1716_: u8 = 0;
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1708_ = lean_st_ref_get(v___y_1706_);
                v_env_1709_ = lean_ctor_get(v___x_1708_, 0);
                lean_inc_ref(v_env_1709_);
                lean_dec(v___x_1708_);
                v___x_1710_ = 0;
                lean_inc(v_constName_1704_);
                v___x_1711_ =
                    l_Lean_Environment_find_x3f(v_env_1709_, v_constName_1704_, v___x_1710_);
                if lean_obj_tag(v___x_1711_) == 0 {
                    v___x_1712_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0___redArg(v_constName_1704_, v___y_1705_, v___y_1706_);
                    return v___x_1712_;
                } else {
                    lean_dec(v_constName_1704_);
                    v_val_1713_ = lean_ctor_get(v___x_1711_, 0);
                    v_isSharedCheck_1720_ = (!lean_is_exclusive(v___x_1711_)) as u8;
                    if v_isSharedCheck_1720_ == 0 {
                        v___x_1715_ = v___x_1711_;
                        v_isShared_1716_ = v_isSharedCheck_1720_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1713_);
                        lean_dec(v___x_1711_);
                        v___x_1715_ = lean_box(0);
                        v_isShared_1716_ = v_isSharedCheck_1720_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1716_ == 0 {
                    lean_ctor_set_tag(v___x_1715_, 0);
                    v___x_1718_ = v___x_1715_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_val_1713_);
                    v___x_1718_ = v_reuseFailAlloc_1719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1718_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0___boxed(
    mut v_constName_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1725_: *mut LeanObject = core::ptr::null_mut();
    v_res_1725_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0(
        v_constName_1721_,
        v___y_1722_,
        v___y_1723_,
    );
    lean_dec(v___y_1723_);
    lean_dec_ref(v___y_1722_);
    return v_res_1725_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__1() -> u64 {
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u64 = 0;
    v___x_1732_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__0;
    v___x_1733_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1732_);
    return v___x_1733_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__2() -> *mut LeanObject {
    let mut v___x_1734_: u64 = 0;
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    v___x_1734_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__1_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__1,
    );
    v___x_1735_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__0;
    v___x_1736_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_1736_, 0, v___x_1735_);
    lean_ctor_set_uint64(
        v___x_1736_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1734_,
    );
    return v___x_1736_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__3() -> *mut LeanObject {
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    v___x_1737_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1737_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4() -> *mut LeanObject {
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    v___x_1738_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__3_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__3,
    );
    v___x_1739_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1739_, 0, v___x_1738_);
    return v___x_1739_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__5() -> *mut LeanObject {
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    v___x_1740_ = lean_box(1);
    v___x_1741_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4);
    v___x_1742_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4,
    );
    v___x_1743_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1743_, 0, v___x_1742_);
    lean_ctor_set(v___x_1743_, 1, v___x_1741_);
    lean_ctor_set(v___x_1743_, 2, v___x_1740_);
    return v___x_1743_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__7() -> *mut LeanObject {
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: u8 = 0;
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    v___x_1746_ = 1;
    v___x_1747_ = lean_unsigned_to_nat(0);
    v___x_1748_ = lean_box(0);
    v___x_1749_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__6;
    v___x_1750_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__5_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__5,
    );
    v___x_1751_ = lean_box(1);
    v___x_1752_ = 0;
    v___x_1753_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__2_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__2,
    );
    v___x_1754_ = lean_alloc_ctor(0, 7, (4) as u32);
    lean_ctor_set(v___x_1754_, 0, v___x_1753_);
    lean_ctor_set(v___x_1754_, 1, v___x_1751_);
    lean_ctor_set(v___x_1754_, 2, v___x_1750_);
    lean_ctor_set(v___x_1754_, 3, v___x_1749_);
    lean_ctor_set(v___x_1754_, 4, v___x_1748_);
    lean_ctor_set(v___x_1754_, 5, v___x_1747_);
    lean_ctor_set(v___x_1754_, 6, v___x_1748_);
    lean_ctor_set_uint8(
        v___x_1754_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
        v___x_1752_,
    );
    lean_ctor_set_uint8(
        v___x_1754_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
        v___x_1752_,
    );
    lean_ctor_set_uint8(
        v___x_1754_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
        v___x_1752_,
    );
    lean_ctor_set_uint8(
        v___x_1754_,
        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
        v___x_1746_,
    );
    return v___x_1754_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__8() -> *mut LeanObject {
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    v___x_1755_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4,
    );
    v___x_1756_ = lean_unsigned_to_nat(0);
    v___x_1757_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1757_, 0, v___x_1756_);
    lean_ctor_set(v___x_1757_, 1, v___x_1756_);
    lean_ctor_set(v___x_1757_, 2, v___x_1756_);
    lean_ctor_set(v___x_1757_, 3, v___x_1756_);
    lean_ctor_set(v___x_1757_, 4, v___x_1755_);
    lean_ctor_set(v___x_1757_, 5, v___x_1755_);
    lean_ctor_set(v___x_1757_, 6, v___x_1755_);
    lean_ctor_set(v___x_1757_, 7, v___x_1755_);
    lean_ctor_set(v___x_1757_, 8, v___x_1755_);
    lean_ctor_set(v___x_1757_, 9, v___x_1755_);
    return v___x_1757_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__9() -> *mut LeanObject {
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    v___x_1758_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4,
    );
    v___x_1759_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_1759_, 0, v___x_1758_);
    lean_ctor_set(v___x_1759_, 1, v___x_1758_);
    lean_ctor_set(v___x_1759_, 2, v___x_1758_);
    lean_ctor_set(v___x_1759_, 3, v___x_1758_);
    lean_ctor_set(v___x_1759_, 4, v___x_1758_);
    lean_ctor_set(v___x_1759_, 5, v___x_1758_);
    return v___x_1759_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__10() -> *mut LeanObject {
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    v___x_1760_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__4,
    );
    v___x_1761_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1761_, 0, v___x_1760_);
    lean_ctor_set(v___x_1761_, 1, v___x_1760_);
    lean_ctor_set(v___x_1761_, 2, v___x_1760_);
    lean_ctor_set(v___x_1761_, 3, v___x_1760_);
    lean_ctor_set(v___x_1761_, 4, v___x_1760_);
    return v___x_1761_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__11() -> *mut LeanObject {
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    v___x_1762_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__10_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__10,
    );
    v___x_1763_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__9___closed__4);
    v___x_1764_ = lean_box(1);
    v___x_1765_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__9_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__9,
    );
    v___x_1766_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__8_once),
        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__8,
    );
    v___x_1767_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1767_, 0, v___x_1766_);
    lean_ctor_set(v___x_1767_, 1, v___x_1765_);
    lean_ctor_set(v___x_1767_, 2, v___x_1764_);
    lean_ctor_set(v___x_1767_, 3, v___x_1763_);
    lean_ctor_set(v___x_1767_, 4, v___x_1762_);
    return v___x_1767_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getOtherDeclBaseType(
    mut v_declName_1768_: *mut LeanObject,
    mut v_us_1769_: *mut LeanObject,
    mut v_a_1770_: *mut LeanObject,
    mut v_a_1771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1777_: u8 = 0;
    let mut v_type_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1800_: u8 = 0;
    let mut v_a_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1804_: u8 = 0;
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_1768_);
                v___x_1773_ =
                    l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0(
                        v_declName_1768_,
                        v_a_1770_,
                        v_a_1771_,
                    );
                if lean_obj_tag(v___x_1773_) == 0 {
                    v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
                    v_isSharedCheck_1800_ = (!lean_is_exclusive(v___x_1773_)) as u8;
                    if v_isSharedCheck_1800_ == 0 {
                        v___x_1776_ = v___x_1773_;
                        v_isShared_1777_ = v_isSharedCheck_1800_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1774_);
                        lean_dec(v___x_1773_);
                        v___x_1776_ = lean_box(0);
                        v_isShared_1777_ = v_isSharedCheck_1800_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_us_1769_);
                    lean_dec(v_declName_1768_);
                    v_a_1801_ = lean_ctor_get(v___x_1773_, 0);
                    v_isSharedCheck_1808_ = (!lean_is_exclusive(v___x_1773_)) as u8;
                    if v_isSharedCheck_1808_ == 0 {
                        v___x_1803_ = v___x_1773_;
                        v_isShared_1804_ = v_isSharedCheck_1808_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1801_);
                        lean_dec(v___x_1773_);
                        v___x_1803_ = lean_box(0);
                        v_isShared_1804_ = v_isSharedCheck_1808_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1785_ = l_Lean_Compiler_LCNF_baseTypeExt;
                v___x_1789_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg(v___x_1785_, v_declName_1768_, v_a_1771_);
                v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
                lean_inc(v_a_1790_);
                lean_dec_ref(v___x_1789_);
                if lean_obj_tag(v_a_1790_) == 0 {
                    v___x_1791_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__7_once
                        ),
                        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__7,
                    );
                    v___x_1792_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__11
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__11_once
                        ),
                        _init_l_Lean_Compiler_LCNF_getOtherDeclBaseType___closed__11,
                    );
                    v___x_1793_ = lean_st_mk_ref(v___x_1792_);
                    v___x_1794_ = l_Lean_ConstantInfo_type(v_a_1774_);
                    v___x_1795_ = l_Lean_Compiler_LCNF_toLCNFType(
                        v___x_1794_,
                        v___x_1791_,
                        v___x_1793_,
                        v_a_1770_,
                        v_a_1771_,
                    );
                    if lean_obj_tag(v___x_1795_) == 0 {
                        v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
                        lean_inc(v_a_1796_);
                        lean_dec_ref_known(v___x_1795_, 1);
                        v___x_1797_ = lean_st_ref_get(v___x_1793_);
                        lean_dec(v___x_1793_);
                        lean_dec(v___x_1797_);
                        v_a_1787_ = v_a_1796_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v___x_1793_);
                        if lean_obj_tag(v___x_1795_) == 0 {
                            v_a_1798_ = lean_ctor_get(v___x_1795_, 0);
                            lean_inc(v_a_1798_);
                            lean_dec_ref_known(v___x_1795_, 1);
                            v_a_1787_ = v_a_1798_;
                            state = 4;
                            continue;
                        } else {
                            lean_del_object(v___x_1776_);
                            lean_dec(v_a_1774_);
                            lean_dec(v_us_1769_);
                            lean_dec(v_declName_1768_);
                            return v___x_1795_;
                        }
                    }
                } else {
                    lean_dec(v_declName_1768_);
                    v_val_1799_ = lean_ctor_get(v_a_1790_, 0);
                    lean_inc(v_val_1799_);
                    lean_dec_ref_known(v_a_1790_, 1);
                    v_type_1779_ = v_val_1799_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1780_ = l_Lean_ConstantInfo_levelParams(v_a_1774_);
                lean_dec(v_a_1774_);
                v___x_1781_ = l_Lean_Expr_instantiateLevelParamsNoCache(
                    v_type_1779_,
                    v___x_1780_,
                    v_us_1769_,
                );
                if v_isShared_1777_ == 0 {
                    lean_ctor_set(v___x_1776_, 0, v___x_1781_);
                    v___x_1783_ = v___x_1776_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1781_);
                    v___x_1783_ = v_reuseFailAlloc_1784_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1783_;
            }
            4 => {
                lean_inc_ref(v_a_1787_);
                v___x_1788_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(v___x_1785_, v_declName_1768_, v_a_1787_, v_a_1771_);
                lean_dec_ref(v___x_1788_);
                v_type_1779_ = v_a_1787_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_1804_ == 0 {
                    v___x_1806_ = v___x_1803_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
                    v___x_1806_ = v_reuseFailAlloc_1807_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getOtherDeclBaseType___boxed(
    mut v_declName_1809_: *mut LeanObject,
    mut v_us_1810_: *mut LeanObject,
    mut v_a_1811_: *mut LeanObject,
    mut v_a_1812_: *mut LeanObject,
    mut v_a_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1814_: *mut LeanObject = core::ptr::null_mut();
    v_res_1814_ = l_Lean_Compiler_LCNF_getOtherDeclBaseType(
        v_declName_1809_,
        v_us_1810_,
        v_a_1811_,
        v_a_1812_,
    );
    lean_dec(v_a_1812_);
    lean_dec_ref(v_a_1811_);
    return v_res_1814_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1(
    mut v_ext_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
    mut v_b_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
    mut v_a_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    v___x_1821_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___redArg(v_ext_1815_, v_a_1816_, v_b_1817_, v_a_1819_);
    return v___x_1821_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1___boxed(
    mut v_ext_1822_: *mut LeanObject,
    mut v_a_1823_: *mut LeanObject,
    mut v_b_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1828_: *mut LeanObject = core::ptr::null_mut();
    v_res_1828_ = l_Lean_Compiler_LCNF_CacheExtension_insert___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__1(v_ext_1822_, v_a_1823_, v_b_1824_, v_a_1825_, v_a_1826_);
    lean_dec(v_a_1826_);
    lean_dec_ref(v_a_1825_);
    return v_res_1828_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2(
    mut v_ext_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
    mut v_a_1831_: *mut LeanObject,
    mut v_a_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    v___x_1834_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___redArg(v_ext_1829_, v_a_1830_, v_a_1832_);
    return v___x_1834_;
}
pub unsafe fn l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2___boxed(
    mut v_ext_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
    mut v_a_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1840_: *mut LeanObject = core::ptr::null_mut();
    v_res_1840_ = l_Lean_Compiler_LCNF_CacheExtension_find_x3f___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__2(v_ext_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
    lean_dec(v_a_1838_);
    lean_dec_ref(v_a_1837_);
    lean_dec(v_a_1836_);
    lean_dec_ref(v_ext_1835_);
    return v_res_1840_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0(
    mut v_00_u03b1_1841_: *mut LeanObject,
    mut v_constName_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    v___x_1846_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0___redArg(v_constName_1842_, v___y_1843_, v___y_1844_);
    return v___x_1846_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0___boxed(
    mut v_00_u03b1_1847_: *mut LeanObject,
    mut v_constName_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
    mut v___y_1850_: *mut LeanObject,
    mut v___y_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1852_: *mut LeanObject = core::ptr::null_mut();
    v_res_1852_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0(v_00_u03b1_1847_, v_constName_1848_, v___y_1849_, v___y_1850_);
    lean_dec(v___y_1850_);
    lean_dec_ref(v___y_1849_);
    return v_res_1852_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1853_: *mut LeanObject,
    mut v_ref_1854_: *mut LeanObject,
    mut v_constName_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___redArg(v_ref_1854_, v_constName_1855_, v___y_1856_, v___y_1857_);
    return v___x_1859_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1860_: *mut LeanObject,
    mut v_ref_1861_: *mut LeanObject,
    mut v_constName_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1866_: *mut LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1(v_00_u03b1_1860_, v_ref_1861_, v_constName_1862_, v___y_1863_, v___y_1864_);
    lean_dec(v___y_1864_);
    lean_dec_ref(v___y_1863_);
    lean_dec(v_ref_1861_);
    return v_res_1866_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1867_: *mut LeanObject,
    mut v_ref_1868_: *mut LeanObject,
    mut v_msg_1869_: *mut LeanObject,
    mut v_declHint_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v___x_1874_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1868_, v_msg_1869_, v_declHint_1870_, v___y_1871_, v___y_1872_);
    return v___x_1874_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1875_: *mut LeanObject,
    mut v_ref_1876_: *mut LeanObject,
    mut v_msg_1877_: *mut LeanObject,
    mut v_declHint_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1882_: *mut LeanObject = core::ptr::null_mut();
    v_res_1882_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1875_, v_ref_1876_, v_msg_1877_, v_declHint_1878_, v___y_1879_, v___y_1880_);
    lean_dec(v___y_1880_);
    lean_dec_ref(v___y_1879_);
    lean_dec(v_ref_1876_);
    return v_res_1882_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_1883_: *mut LeanObject,
    mut v_declHint_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    v___x_1888_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1883_, v_declHint_1884_, v___y_1886_);
    return v___x_1888_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_1889_: *mut LeanObject,
    mut v_declHint_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1894_: *mut LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1889_, v_declHint_1890_, v___y_1891_, v___y_1892_);
    lean_dec(v___y_1892_);
    lean_dec_ref(v___y_1891_);
    return v_res_1894_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_1895_: *mut LeanObject,
    mut v_ref_1896_: *mut LeanObject,
    mut v_msg_1897_: *mut LeanObject,
    mut v___y_1898_: *mut LeanObject,
    mut v___y_1899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    v___x_1901_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1896_, v_msg_1897_, v___y_1898_, v___y_1899_);
    return v___x_1901_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_1902_: *mut LeanObject,
    mut v_ref_1903_: *mut LeanObject,
    mut v_msg_1904_: *mut LeanObject,
    mut v___y_1905_: *mut LeanObject,
    mut v___y_1906_: *mut LeanObject,
    mut v___y_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1908_: *mut LeanObject = core::ptr::null_mut();
    v_res_1908_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1902_, v_ref_1903_, v_msg_1904_, v___y_1905_, v___y_1906_);
    lean_dec(v___y_1906_);
    lean_dec_ref(v___y_1905_);
    lean_dec(v_ref_1903_);
    return v_res_1908_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(
    mut v_00_u03b1_1909_: *mut LeanObject,
    mut v_msg_1910_: *mut LeanObject,
    mut v___y_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    v___x_1914_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_msg_1910_, v___y_1911_, v___y_1912_);
    return v___x_1914_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(
    mut v_00_u03b1_1915_: *mut LeanObject,
    mut v_msg_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
    mut v___y_1918_: *mut LeanObject,
    mut v___y_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1920_: *mut LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getOtherDeclBaseType_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_1915_, v_msg_1916_, v___y_1917_, v___y_1918_);
    lean_dec(v___y_1918_);
    lean_dec_ref(v___y_1917_);
    return v_res_1920_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_BaseTypes(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_BaseTypes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_BaseTypes_124699504____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_baseTypeExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Compiler_LCNF_baseTypeExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_BaseTypes(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_BaseTypes(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_BaseTypes(builtin);
}
