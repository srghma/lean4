// Lean compiler output
// Module: Lean.Linter.Init
// Imports: Lean.MonadEnv Init.Data.Function
use crate::r#gen::Init::Data::Function::{
    initialize_Init_Data_Function, runtime_initialize_Init_Data_Function,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg,
};
use crate::r#gen::Lean::Log::l_Lean_logWarningAt___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasTag, l_Lean_MessageData_note, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::MonadEnv::{initialize_Lean_MonadEnv, runtime_initialize_Lean_MonadEnv};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static mut l_Lean_Linter_instEmptyCollectionLinterSets___aux__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Linter_instEmptyCollectionLinterSets: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Linter_instInhabitedLinterSets___aux__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Linter_instInhabitedLinterSets: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [108, 105, 110, 116, 101, 114, 83, 101, 116, 115, 69, 120, 116, 0]};
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,5476513427391162549 as *mut LeanObject] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject,12638910018443785458 as *mut LeanObject] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 110, 97, 98, 108, 101, 32, 97, 108, 108, 32, 108, 105, 110, 116, 101, 114, 115, 0]};
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject,6326339448686113589 as *mut LeanObject] };
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject,3607167505933248393 as *mut LeanObject] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 116, 114, 97, 0]};
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject,5701751079888345786 as *mut LeanObject] };
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value) as *mut LeanObject,8383467597245298465 as *mut LeanObject] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value: LeanStringObject<170> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 170, m_capacity: 170, m_length: 167, m_data: [101, 110, 97, 98, 108, 101, 115, 32, 116, 104, 101, 32, 115, 101, 116, 32, 111, 102, 32, 101, 120, 116, 114, 97, 32, 108, 105, 110, 116, 101, 114, 115, 32, 226, 128, 148, 32, 108, 105, 110, 116, 101, 114, 115, 32, 116, 104, 97, 116, 32, 97, 114, 101, 32, 116, 117, 114, 110, 101, 100, 32, 111, 102, 102, 32, 98, 121, 32, 100, 101, 102, 97, 117, 108, 116, 32, 97, 110, 100, 32, 111, 110, 108, 121, 32, 97, 118, 97, 105, 108, 97, 98, 108, 101, 32, 118, 105, 97, 32, 96, 108, 97, 107, 101, 32, 108, 105, 110, 116, 96, 46, 32, 65, 110, 32, 101, 120, 116, 114, 97, 32, 108, 105, 110, 116, 101, 114, 32, 101, 97, 114, 108, 121, 45, 114, 101, 116, 117, 114, 110, 115, 32, 117, 110, 108, 101, 115, 115, 32, 116, 104, 105, 115, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 116, 114, 117, 101, 46, 0]};
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value) as *mut LeanObject,6326339448686113589 as *mut LeanObject] };
pub static l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value) as *mut LeanObject,12057260084657374522 as *mut LeanObject] };
static mut l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_Linter_linterMessageTag___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [95, 108, 105, 110, 116, 101, 114, 0],
    };
static mut l_Lean_Linter_linterMessageTag___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_linterMessageTag___closed__0_value) as *mut LeanObject;
static l_Lean_Linter_linterMessageTag___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Linter_linterMessageTag___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_linterMessageTag___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__value) as *mut LeanObject,8071394701935581384 as *mut LeanObject] };
pub static l_Lean_Linter_linterMessageTag___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Linter_linterMessageTag___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Linter_linterMessageTag___closed__0_value) as *mut LeanObject,
        11561939393814595044 as *mut LeanObject,
    ],
};
static mut l_Lean_Linter_linterMessageTag___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_linterMessageTag___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_Linter_linterMessageTag: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_linterMessageTag___closed__1_value) as *mut LeanObject;
pub static l_Lean_Linter_logLint___redArg___closed__0_value: LeanStringObject<46> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 46,
        m_capacity: 46,
        m_length: 45,
        m_data: [
            84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32,
            100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116,
            95, 111, 112, 116, 105, 111, 110, 32, 0,
        ],
    };
static mut l_Lean_Linter_logLint___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_logLint___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___redArg___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [32, 102, 97, 108, 115, 101, 96, 0],
    };
static mut l_Lean_Linter_logLint___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Linter_logLint___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_Linter_logLint___redArg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Linter_logLint___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MessageData_isLinterMessage___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MessageData_isLinterMessage___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MessageData_isLinterMessage___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MessageData_isLinterMessage___closed__0_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Linter_instEmptyCollectionLinterSets___aux__1() -> *mut LeanObject {
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    v___x_614_ = lean_box(1);
    return v___x_614_;
}
pub unsafe fn _init_l_Lean_Linter_instEmptyCollectionLinterSets() -> *mut LeanObject {
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    v___x_615_ = lean_box(1);
    return v___x_615_;
}
pub unsafe fn _init_l_Lean_Linter_instInhabitedLinterSets___aux__1() -> *mut LeanObject {
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    v___x_616_ = lean_box(1);
    return v___x_616_;
}
pub unsafe fn _init_l_Lean_Linter_instInhabitedLinterSets() -> *mut LeanObject {
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    v___x_617_ = lean_box(1);
    return v___x_617_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(
    mut v_t_618_: *mut LeanObject,
    mut v_k_619_: *mut LeanObject,
    mut v_fallback_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_618_) == 0 {
                    v_k_621_ = lean_ctor_get(v_t_618_, 1);
                    v_v_622_ = lean_ctor_get(v_t_618_, 2);
                    v_l_623_ = lean_ctor_get(v_t_618_, 3);
                    v_r_624_ = lean_ctor_get(v_t_618_, 4);
                    v___x_625_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_619_, v_k_621_);
                    match v___x_625_ {
                        0 => {
                            v_t_618_ = v_l_623_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_622_);
                            return v_v_622_;
                        }
                        _ => {
                            v_t_618_ = v_r_624_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_fallback_620_);
                    return v_fallback_620_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg___boxed(
    mut v_t_628_: *mut LeanObject,
    mut v_k_629_: *mut LeanObject,
    mut v_fallback_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_631_: *mut LeanObject = core::ptr::null_mut();
    v_res_631_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_t_628_, v_k_629_, v_fallback_630_);
    lean_dec(v_fallback_630_);
    lean_dec(v_k_629_);
    lean_dec(v_t_628_);
    return v_res_631_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(
    mut v_setName_634_: *mut LeanObject,
    mut v_init_635_: *mut LeanObject,
    mut v_x_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_636_) == 0 {
                    v_k_637_ = lean_ctor_get(v_x_636_, 1);
                    lean_inc(v_k_637_);
                    v_l_638_ = lean_ctor_get(v_x_636_, 3);
                    lean_inc(v_l_638_);
                    v_r_639_ = lean_ctor_get(v_x_636_, 4);
                    lean_inc(v_r_639_);
                    lean_dec_ref_known(v_x_636_, 5);
                    lean_inc_n(v_setName_634_, 2);
                    v___x_640_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_setName_634_, v_init_635_, v_l_638_);
                    v___x_641_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0;
                    v___x_642_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v___x_640_, v_k_637_, v___x_641_);
                    v___x_643_ = lean_array_push(v___x_642_, v_setName_634_);
                    v___x_644_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_637_, v___x_643_, v___x_640_);
                    v_init_635_ = v___x_644_;
                    v_x_636_ = v_r_639_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_setName_634_);
                    return v_init_635_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_insertLinterSetEntry(
    mut v_map_646_: *mut LeanObject,
    mut v_setName_647_: *mut LeanObject,
    mut v_options_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    v___x_649_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_setName_647_, v_map_646_, v_options_648_);
    return v___x_649_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0(
    mut v_00_u03b4_650_: *mut LeanObject,
    mut v_t_651_: *mut LeanObject,
    mut v_k_652_: *mut LeanObject,
    mut v_fallback_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    v___x_654_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_t_651_, v_k_652_, v_fallback_653_);
    return v___x_654_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___boxed(
    mut v_00_u03b4_655_: *mut LeanObject,
    mut v_t_656_: *mut LeanObject,
    mut v_k_657_: *mut LeanObject,
    mut v_fallback_658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_659_: *mut LeanObject = core::ptr::null_mut();
    v_res_659_ =
        l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0(
            v_00_u03b4_655_,
            v_t_656_,
            v_k_657_,
            v_fallback_658_,
        );
    lean_dec(v_fallback_658_);
    lean_dec(v_k_657_);
    lean_dec(v_t_656_);
    return v_res_659_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1(
    mut v_setName_660_: *mut LeanObject,
    mut v_init_661_: *mut LeanObject,
    mut v_t_662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    v___x_663_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_setName_660_, v_init_661_, v_t_662_);
    return v___x_663_;
}
pub unsafe fn l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_(
    mut v_x_664_: *mut LeanObject,
    mut v___y_665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    v_fst_666_ = lean_ctor_get(v___y_665_, 0);
    lean_inc(v_fst_666_);
    v_snd_667_ = lean_ctor_get(v___y_665_, 1);
    lean_inc(v_snd_667_);
    lean_dec_ref(v___y_665_);
    v___x_668_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_666_, v_x_664_, v_snd_667_);
    return v___x_668_;
}
pub unsafe fn l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_(
    mut v_es_669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    v___x_670_ = lean_array_mk(v_es_669_);
    return v___x_670_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_671_: *mut LeanObject,
    mut v_i_672_: usize,
    mut v_stop_673_: usize,
    mut v_b_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_675_: u8 = 0;
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: usize = 0;
    let mut v___x_681_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_675_ = lean_usize_dec_eq(v_i_672_, v_stop_673_);
                if v___x_675_ == 0 {
                    v___x_676_ = lean_array_uget_borrowed(v_as_671_, v_i_672_);
                    v_fst_677_ = lean_ctor_get(v___x_676_, 0);
                    v_snd_678_ = lean_ctor_get(v___x_676_, 1);
                    lean_inc(v_snd_678_);
                    lean_inc(v_fst_677_);
                    v___x_679_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_677_, v_b_674_, v_snd_678_);
                    v___x_680_ = 1usize;
                    v___x_681_ = lean_usize_add(v_i_672_, v___x_680_);
                    v_i_672_ = v___x_681_;
                    v_b_674_ = v___x_679_;
                    state = 0;
                    continue;
                } else {
                    return v_b_674_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_as_683_: *mut LeanObject,
    mut v_i_684_: *mut LeanObject,
    mut v_stop_685_: *mut LeanObject,
    mut v_b_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_687_: usize = 0;
    let mut v_stop_boxed_688_: usize = 0;
    let mut v_res_689_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_687_ = lean_unbox_usize(v_i_684_);
    lean_dec(v_i_684_);
    v_stop_boxed_688_ = lean_unbox_usize(v_stop_685_);
    lean_dec(v_stop_685_);
    v_res_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0_spec__0(v_as_683_, v_i_boxed_687_, v_stop_boxed_688_, v_b_686_);
    lean_dec_ref(v_as_683_);
    return v_res_689_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0_spec__1(
    mut v_as_690_: *mut LeanObject,
    mut v_i_691_: usize,
    mut v_stop_692_: usize,
    mut v_b_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: usize = 0;
    let mut v___x_697_: usize = 0;
    let mut v___x_699_: u8 = 0;
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: u8 = 0;
    let mut v___x_704_: u8 = 0;
    let mut v___x_705_: usize = 0;
    let mut v___x_706_: usize = 0;
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: usize = 0;
    let mut v___x_709_: usize = 0;
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_699_ = lean_usize_dec_eq(v_i_691_, v_stop_692_);
                if v___x_699_ == 0 {
                    v___x_700_ = lean_array_uget_borrowed(v_as_690_, v_i_691_);
                    v___x_701_ = lean_unsigned_to_nat(0);
                    v___x_702_ = lean_array_get_size(v___x_700_);
                    v___x_703_ = lean_nat_dec_lt(v___x_701_, v___x_702_);
                    if v___x_703_ == 0 {
                        v___y_695_ = v_b_693_;
                        state = 1;
                        continue;
                    } else {
                        v___x_704_ = lean_nat_dec_le(v___x_702_, v___x_702_);
                        if v___x_704_ == 0 {
                            if v___x_703_ == 0 {
                                v___y_695_ = v_b_693_;
                                state = 1;
                                continue;
                            } else {
                                v___x_705_ = 0usize;
                                v___x_706_ = lean_usize_of_nat(v___x_702_);
                                v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0_spec__0(v___x_700_, v___x_705_, v___x_706_, v_b_693_);
                                v___y_695_ = v___x_707_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_708_ = 0usize;
                            v___x_709_ = lean_usize_of_nat(v___x_702_);
                            v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0_spec__0(v___x_700_, v___x_708_, v___x_709_, v_b_693_);
                            v___y_695_ = v___x_710_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_693_;
                }
            }
            1 => {
                v___x_696_ = 1usize;
                v___x_697_ = lean_usize_add(v_i_691_, v___x_696_);
                v_i_691_ = v___x_697_;
                v_b_693_ = v___y_695_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0_spec__1___boxed(
    mut v_as_711_: *mut LeanObject,
    mut v_i_712_: *mut LeanObject,
    mut v_stop_713_: *mut LeanObject,
    mut v_b_714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_715_: usize = 0;
    let mut v_stop_boxed_716_: usize = 0;
    let mut v_res_717_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_715_ = lean_unbox_usize(v_i_712_);
    lean_dec(v_i_712_);
    v_stop_boxed_716_ = lean_unbox_usize(v_stop_713_);
    lean_dec(v_stop_713_);
    v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0_spec__1(v_as_711_, v_i_boxed_715_, v_stop_boxed_716_, v_b_714_);
    lean_dec_ref(v_as_711_);
    return v_res_717_;
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0(
    mut v_initState_718_: *mut LeanObject,
    mut v_as_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    v___x_720_ = lean_unsigned_to_nat(0);
    v___x_721_ = lean_array_get_size(v_as_719_);
    v___x_722_ = lean_nat_dec_lt(v___x_720_, v___x_721_);
    if v___x_722_ == 0 {
        return v_initState_718_;
    } else {
        let mut v___x_723_: u8 = 0;
        v___x_723_ = lean_nat_dec_le(v___x_721_, v___x_721_);
        if v___x_723_ == 0 {
            if v___x_722_ == 0 {
                return v_initState_718_;
            } else {
                let mut v___x_724_: usize = 0;
                let mut v___x_725_: usize = 0;
                let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
                v___x_724_ = 0usize;
                v___x_725_ = lean_usize_of_nat(v___x_721_);
                v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0_spec__1(v_as_719_, v___x_724_, v___x_725_, v_initState_718_);
                return v___x_726_;
            }
        } else {
            let mut v___x_727_: usize = 0;
            let mut v___x_728_: usize = 0;
            let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
            v___x_727_ = 0usize;
            v___x_728_ = lean_usize_of_nat(v___x_721_);
            v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0_spec__1(v_as_719_, v___x_727_, v___x_728_, v_initState_718_);
            return v___x_729_;
        }
    }
}
pub unsafe fn l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0___boxed(
    mut v_initState_730_: *mut LeanObject,
    mut v_as_731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_732_: *mut LeanObject = core::ptr::null_mut();
    v_res_732_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2__spec__0(v_initState_730_, v_as_731_);
    lean_dec_ref(v_as_731_);
    return v_res_732_;
}
pub unsafe fn l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    v___x_752_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_;
    v___x_753_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_752_);
    return v___x_753_;
}
pub unsafe fn l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2____boxed(
    mut v_a_754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_755_: *mut LeanObject = core::ptr::null_mut();
    v_res_755_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_();
    return v_res_755_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_get___redArg(
    mut v_inst_756_: *mut LeanObject,
    mut v_o_757_: *mut LeanObject,
    mut v_k_758_: *mut LeanObject,
    mut v_defVal_759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toOptions_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    v_toOptions_760_ = lean_ctor_get(v_o_757_, 0);
    v_map_761_ = lean_ctor_get(v_toOptions_760_, 0);
    v_ofDataValue_x3f_762_ = lean_ctor_get(v_inst_756_, 1);
    lean_inc_ref(v_ofDataValue_x3f_762_);
    lean_dec_ref(v_inst_756_);
    v___x_763_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_761_, v_k_758_,
        );
    if lean_obj_tag(v___x_763_) == 0 {
        lean_dec_ref(v_ofDataValue_x3f_762_);
        lean_inc(v_defVal_759_);
        return v_defVal_759_;
    } else {
        let mut v_val_764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
        v_val_764_ = lean_ctor_get(v___x_763_, 0);
        lean_inc(v_val_764_);
        lean_dec_ref_known(v___x_763_, 1);
        v___x_765_ = lean_apply_1(v_ofDataValue_x3f_762_, v_val_764_);
        if lean_obj_tag(v___x_765_) == 0 {
            lean_inc(v_defVal_759_);
            return v_defVal_759_;
        } else {
            let mut v_val_766_: *mut LeanObject = core::ptr::null_mut();
            v_val_766_ = lean_ctor_get(v___x_765_, 0);
            lean_inc(v_val_766_);
            lean_dec_ref_known(v___x_765_, 1);
            return v_val_766_;
        }
    }
}
pub unsafe fn l_Lean_Linter_LinterOptions_get___redArg___boxed(
    mut v_inst_767_: *mut LeanObject,
    mut v_o_768_: *mut LeanObject,
    mut v_k_769_: *mut LeanObject,
    mut v_defVal_770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_771_: *mut LeanObject = core::ptr::null_mut();
    v_res_771_ =
        l_Lean_Linter_LinterOptions_get___redArg(v_inst_767_, v_o_768_, v_k_769_, v_defVal_770_);
    lean_dec(v_defVal_770_);
    lean_dec(v_k_769_);
    lean_dec_ref(v_o_768_);
    return v_res_771_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_get(
    mut v_00_u03b1_772_: *mut LeanObject,
    mut v_inst_773_: *mut LeanObject,
    mut v_o_774_: *mut LeanObject,
    mut v_k_775_: *mut LeanObject,
    mut v_defVal_776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    v___x_777_ =
        l_Lean_Linter_LinterOptions_get___redArg(v_inst_773_, v_o_774_, v_k_775_, v_defVal_776_);
    return v___x_777_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_get___boxed(
    mut v_00_u03b1_778_: *mut LeanObject,
    mut v_inst_779_: *mut LeanObject,
    mut v_o_780_: *mut LeanObject,
    mut v_k_781_: *mut LeanObject,
    mut v_defVal_782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_783_: *mut LeanObject = core::ptr::null_mut();
    v_res_783_ = l_Lean_Linter_LinterOptions_get(
        v_00_u03b1_778_,
        v_inst_779_,
        v_o_780_,
        v_k_781_,
        v_defVal_782_,
    );
    lean_dec(v_defVal_782_);
    lean_dec(v_k_781_);
    lean_dec_ref(v_o_780_);
    return v_res_783_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_get_x3f___redArg(
    mut v_inst_784_: *mut LeanObject,
    mut v_o_785_: *mut LeanObject,
    mut v_k_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toOptions_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    v_toOptions_787_ = lean_ctor_get(v_o_785_, 0);
    v_map_788_ = lean_ctor_get(v_toOptions_787_, 0);
    v_ofDataValue_x3f_789_ = lean_ctor_get(v_inst_784_, 1);
    lean_inc_ref(v_ofDataValue_x3f_789_);
    lean_dec_ref(v_inst_784_);
    v___x_790_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_788_, v_k_786_,
        );
    if lean_obj_tag(v___x_790_) == 0 {
        let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ofDataValue_x3f_789_);
        v___x_791_ = lean_box(0);
        return v___x_791_;
    } else {
        let mut v_val_792_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
        v_val_792_ = lean_ctor_get(v___x_790_, 0);
        lean_inc(v_val_792_);
        lean_dec_ref_known(v___x_790_, 1);
        v___x_793_ = lean_apply_1(v_ofDataValue_x3f_789_, v_val_792_);
        return v___x_793_;
    }
}
pub unsafe fn l_Lean_Linter_LinterOptions_get_x3f___redArg___boxed(
    mut v_inst_794_: *mut LeanObject,
    mut v_o_795_: *mut LeanObject,
    mut v_k_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_797_: *mut LeanObject = core::ptr::null_mut();
    v_res_797_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_794_, v_o_795_, v_k_796_);
    lean_dec(v_k_796_);
    lean_dec_ref(v_o_795_);
    return v_res_797_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_get_x3f(
    mut v_00_u03b1_798_: *mut LeanObject,
    mut v_inst_799_: *mut LeanObject,
    mut v_o_800_: *mut LeanObject,
    mut v_k_801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    v___x_802_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_799_, v_o_800_, v_k_801_);
    return v___x_802_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_get_x3f___boxed(
    mut v_00_u03b1_803_: *mut LeanObject,
    mut v_inst_804_: *mut LeanObject,
    mut v_o_805_: *mut LeanObject,
    mut v_k_806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_807_: *mut LeanObject = core::ptr::null_mut();
    v_res_807_ =
        l_Lean_Linter_LinterOptions_get_x3f(v_00_u03b1_803_, v_inst_804_, v_o_805_, v_k_806_);
    lean_dec(v_k_806_);
    lean_dec_ref(v_o_805_);
    return v_res_807_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___redArg___lam__0(
    mut v___x_808_: *mut LeanObject,
    mut v_o_809_: *mut LeanObject,
    mut v_toPure_810_: *mut LeanObject,
    mut v_____do__lift_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_linterSets_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    v___x_812_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_813_ = lean_ctor_get(v___x_812_, 0);
    v_asyncMode_814_ = lean_ctor_get(v_toEnvExtension_813_, 2);
    v___x_815_ = lean_box(0);
    v_linterSets_816_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_808_,
        v___x_812_,
        v_____do__lift_811_,
        v_asyncMode_814_,
        v___x_815_,
    );
    v___x_817_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_817_, 0, v_o_809_);
    lean_ctor_set(v___x_817_, 1, v_linterSets_816_);
    v___x_818_ = lean_apply_2(v_toPure_810_, lean_box(0), v___x_817_);
    return v___x_818_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___redArg(
    mut v_inst_819_: *mut LeanObject,
    mut v_inst_820_: *mut LeanObject,
    mut v_o_821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_822_ = lean_ctor_get(v_inst_819_, 0);
    lean_inc_ref(v_toApplicative_822_);
    v_toBind_823_ = lean_ctor_get(v_inst_819_, 1);
    lean_inc(v_toBind_823_);
    lean_dec_ref(v_inst_819_);
    v_getEnv_824_ = lean_ctor_get(v_inst_820_, 0);
    lean_inc(v_getEnv_824_);
    lean_dec_ref(v_inst_820_);
    v_toPure_825_ = lean_ctor_get(v_toApplicative_822_, 1);
    lean_inc(v_toPure_825_);
    lean_dec_ref(v_toApplicative_822_);
    v___x_826_ = lean_box(1);
    v___f_827_ = lean_alloc_closure(
        l_Lean_Options_toLinterOptions___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_827_, 0, v___x_826_);
    lean_closure_set(v___f_827_, 1, v_o_821_);
    lean_closure_set(v___f_827_, 2, v_toPure_825_);
    v___x_828_ = lean_apply_4(
        v_toBind_823_,
        lean_box(0),
        lean_box(0),
        v_getEnv_824_,
        v___f_827_,
    );
    return v___x_828_;
}
pub unsafe fn l_Lean_Options_toLinterOptions(
    mut v_m_829_: *mut LeanObject,
    mut v_inst_830_: *mut LeanObject,
    mut v_inst_831_: *mut LeanObject,
    mut v_o_832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    v___x_833_ = l_Lean_Options_toLinterOptions___redArg(v_inst_830_, v_inst_831_, v_o_832_);
    return v___x_833_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_getSet___redArg(
    mut v_o_834_: *mut LeanObject,
    mut v_opt_835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_linterSets_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    v_linterSets_836_ = lean_ctor_get(v_o_834_, 1);
    v_name_837_ = lean_ctor_get(v_opt_835_, 0);
    v___x_838_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0;
    v___x_839_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_linterSets_836_, v_name_837_, v___x_838_);
    return v___x_839_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_getSet___redArg___boxed(
    mut v_o_840_: *mut LeanObject,
    mut v_opt_841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_842_: *mut LeanObject = core::ptr::null_mut();
    v_res_842_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_840_, v_opt_841_);
    lean_dec_ref(v_opt_841_);
    lean_dec_ref(v_o_840_);
    return v_res_842_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_getSet(
    mut v_00_u03b1_843_: *mut LeanObject,
    mut v_o_844_: *mut LeanObject,
    mut v_opt_845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    v___x_846_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_844_, v_opt_845_);
    return v___x_846_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_getSet___boxed(
    mut v_00_u03b1_847_: *mut LeanObject,
    mut v_o_848_: *mut LeanObject,
    mut v_opt_849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_850_: *mut LeanObject = core::ptr::null_mut();
    v_res_850_ = l_Lean_Linter_LinterOptions_getSet(v_00_u03b1_847_, v_o_848_, v_opt_849_);
    lean_dec_ref(v_opt_849_);
    lean_dec_ref(v_o_848_);
    return v_res_850_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___redArg___lam__0(
    mut v_inst_851_: *mut LeanObject,
    mut v_inst_852_: *mut LeanObject,
    mut v_____do__lift_853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    v___x_854_ =
        l_Lean_Options_toLinterOptions___redArg(v_inst_851_, v_inst_852_, v_____do__lift_853_);
    return v___x_854_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___redArg(
    mut v_inst_855_: *mut LeanObject,
    mut v_inst_856_: *mut LeanObject,
    mut v_inst_857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_858_ = lean_ctor_get(v_inst_855_, 1);
    lean_inc(v_toBind_858_);
    v___f_859_ = lean_alloc_closure(
        l_Lean_Linter_getLinterOptions___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_859_, 0, v_inst_855_);
    lean_closure_set(v___f_859_, 1, v_inst_857_);
    v___x_860_ = lean_apply_4(
        v_toBind_858_,
        lean_box(0),
        lean_box(0),
        v_inst_856_,
        v___f_859_,
    );
    return v___x_860_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions(
    mut v_m_861_: *mut LeanObject,
    mut v_inst_862_: *mut LeanObject,
    mut v_inst_863_: *mut LeanObject,
    mut v_inst_864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    v___x_865_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_862_, v_inst_863_, v_inst_864_);
    return v___x_865_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(
    mut v_name_866_: *mut LeanObject,
    mut v_decl_867_: *mut LeanObject,
    mut v_ref_868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: u8 = 0;
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_879_: u8 = 0;
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_884_: u8 = 0;
    let mut v_unused_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_889_: u8 = 0;
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_870_ = lean_ctor_get(v_decl_867_, 0);
                v_descr_871_ = lean_ctor_get(v_decl_867_, 1);
                v_deprecation_x3f_872_ = lean_ctor_get(v_decl_867_, 2);
                v___x_873_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_874_ = (lean_unbox(v_defValue_870_) as u8);
                lean_ctor_set_uint8(v___x_873_, 0 as u32, v___x_874_);
                lean_inc(v_deprecation_x3f_872_);
                lean_inc_ref(v_descr_871_);
                lean_inc_n(v_name_866_, 2);
                v___x_875_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_875_, 0, v_name_866_);
                lean_ctor_set(v___x_875_, 1, v_ref_868_);
                lean_ctor_set(v___x_875_, 2, v___x_873_);
                lean_ctor_set(v___x_875_, 3, v_descr_871_);
                lean_ctor_set(v___x_875_, 4, v_deprecation_x3f_872_);
                v___x_876_ = lean_register_option(v_name_866_, v___x_875_);
                if lean_obj_tag(v___x_876_) == 0 {
                    v_isSharedCheck_884_ = (!lean_is_exclusive(v___x_876_)) as u8;
                    if v_isSharedCheck_884_ == 0 {
                        v_unused_885_ = lean_ctor_get(v___x_876_, 0);
                        lean_dec(v_unused_885_);
                        v___x_878_ = v___x_876_;
                        v_isShared_879_ = v_isSharedCheck_884_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_876_);
                        v___x_878_ = lean_box(0);
                        v_isShared_879_ = v_isSharedCheck_884_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_866_);
                    v_a_886_ = lean_ctor_get(v___x_876_, 0);
                    v_isSharedCheck_893_ = (!lean_is_exclusive(v___x_876_)) as u8;
                    if v_isSharedCheck_893_ == 0 {
                        v___x_888_ = v___x_876_;
                        v_isShared_889_ = v_isSharedCheck_893_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_886_);
                        lean_dec(v___x_876_);
                        v___x_888_ = lean_box(0);
                        v_isShared_889_ = v_isSharedCheck_893_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_870_);
                v___x_880_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_880_, 0, v_name_866_);
                lean_ctor_set(v___x_880_, 1, v_defValue_870_);
                if v_isShared_879_ == 0 {
                    lean_ctor_set(v___x_878_, 0, v___x_880_);
                    v___x_882_ = v___x_878_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
                    v___x_882_ = v_reuseFailAlloc_883_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_882_;
            }
            3 => {
                if v_isShared_889_ == 0 {
                    v___x_891_ = v___x_888_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
                    v___x_891_ = v_reuseFailAlloc_892_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_894_: *mut LeanObject,
    mut v_decl_895_: *mut LeanObject,
    mut v_ref_896_: *mut LeanObject,
    mut v_a_897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_898_: *mut LeanObject = core::ptr::null_mut();
    v_res_898_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v_name_894_, v_decl_895_, v_ref_896_);
    lean_dec_ref(v_decl_895_);
    return v_res_898_;
}
pub unsafe fn l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    v___x_916_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_;
    v___x_917_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_;
    v___x_918_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_;
    v___x_919_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_916_, v___x_917_, v___x_918_);
    return v___x_919_;
}
pub unsafe fn l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4____boxed(
    mut v_a_920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_921_: *mut LeanObject = core::ptr::null_mut();
    v_res_921_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_();
    return v_res_921_;
}
pub unsafe fn l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    v___x_938_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_;
    v___x_939_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_;
    v___x_940_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_;
    v___x_941_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_938_, v___x_939_, v___x_940_);
    return v___x_941_;
}
pub unsafe fn l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4____boxed(
    mut v_a_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_943_: *mut LeanObject = core::ptr::null_mut();
    v_res_943_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_();
    return v_res_943_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(
    mut v_o_944_: *mut LeanObject,
    mut v_k_945_: *mut LeanObject,
    mut v_defVal_946_: u8,
) -> u8 {
    let mut v_toOptions_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    v_toOptions_947_ = lean_ctor_get(v_o_944_, 0);
    v_map_948_ = lean_ctor_get(v_toOptions_947_, 0);
    v___x_949_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_948_, v_k_945_,
        );
    if lean_obj_tag(v___x_949_) == 0 {
        return v_defVal_946_;
    } else {
        let mut v_val_950_: *mut LeanObject = core::ptr::null_mut();
        v_val_950_ = lean_ctor_get(v___x_949_, 0);
        lean_inc(v_val_950_);
        lean_dec_ref_known(v___x_949_, 1);
        if lean_obj_tag(v_val_950_) == 1 {
            let mut v_v_951_: u8 = 0;
            v_v_951_ = lean_ctor_get_uint8(v_val_950_, 0 as u32);
            lean_dec_ref_known(v_val_950_, 0);
            return v_v_951_;
        } else {
            lean_dec(v_val_950_);
            return v_defVal_946_;
        }
    }
}
pub unsafe fn l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0___boxed(
    mut v_o_952_: *mut LeanObject,
    mut v_k_953_: *mut LeanObject,
    mut v_defVal_954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defVal_boxed_955_: u8 = 0;
    let mut v_res_956_: u8 = 0;
    let mut v_r_957_: *mut LeanObject = core::ptr::null_mut();
    v_defVal_boxed_955_ = (lean_unbox(v_defVal_954_) as u8);
    v_res_956_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(
        v_o_952_,
        v_k_953_,
        v_defVal_boxed_955_,
    );
    lean_dec(v_k_953_);
    lean_dec_ref(v_o_952_);
    v_r_957_ = lean_box((v_res_956_) as usize);
    return v_r_957_;
}
pub unsafe fn l_Lean_Linter_getLinterAll(
    mut v_o_958_: *mut LeanObject,
    mut v_defValue_959_: u8,
) -> u8 {
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: u8 = 0;
    v___x_960_ = l_Lean_Linter_linter_all;
    v_name_961_ = lean_ctor_get(v___x_960_, 0);
    v___x_962_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(
        v_o_958_,
        v_name_961_,
        v_defValue_959_,
    );
    return v___x_962_;
}
pub unsafe fn l_Lean_Linter_getLinterAll___boxed(
    mut v_o_963_: *mut LeanObject,
    mut v_defValue_964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_boxed_965_: u8 = 0;
    let mut v_res_966_: u8 = 0;
    let mut v_r_967_: *mut LeanObject = core::ptr::null_mut();
    v_defValue_boxed_965_ = (lean_unbox(v_defValue_964_) as u8);
    v_res_966_ = l_Lean_Linter_getLinterAll(v_o_963_, v_defValue_boxed_965_);
    lean_dec_ref(v_o_963_);
    v_r_967_ = lean_box((v_res_966_) as usize);
    return v_r_967_;
}
pub unsafe fn l_Lean_Linter_getLinterExtra(
    mut v_o_968_: *mut LeanObject,
    mut v_defValue_969_: u8,
) -> u8 {
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: u8 = 0;
    v___x_970_ = l_Lean_Linter_linter_extra;
    v_name_971_ = lean_ctor_get(v___x_970_, 0);
    v___x_972_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(
        v_o_968_,
        v_name_971_,
        v_defValue_969_,
    );
    return v___x_972_;
}
pub unsafe fn l_Lean_Linter_getLinterExtra___boxed(
    mut v_o_973_: *mut LeanObject,
    mut v_defValue_974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_boxed_975_: u8 = 0;
    let mut v_res_976_: u8 = 0;
    let mut v_r_977_: *mut LeanObject = core::ptr::null_mut();
    v_defValue_boxed_975_ = (lean_unbox(v_defValue_974_) as u8);
    v_res_976_ = l_Lean_Linter_getLinterExtra(v_o_973_, v_defValue_boxed_975_);
    lean_dec_ref(v_o_973_);
    v_r_977_ = lean_box((v_res_976_) as usize);
    return v_r_977_;
}
pub unsafe fn l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(
    mut v_o_978_: *mut LeanObject,
    mut v_k_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toOptions_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_987_: u8 = 0;
    let mut v_v_988_: u8 = 0;
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toOptions_980_ = lean_ctor_get(v_o_978_, 0);
                v_map_981_ = lean_ctor_get(v_toOptions_980_, 0);
                v___x_982_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_981_, v_k_979_);
                if lean_obj_tag(v___x_982_) == 0 {
                    v___x_983_ = lean_box(0);
                    return v___x_983_;
                } else {
                    v_val_984_ = lean_ctor_get(v___x_982_, 0);
                    v_isSharedCheck_994_ = (!lean_is_exclusive(v___x_982_)) as u8;
                    if v_isSharedCheck_994_ == 0 {
                        v___x_986_ = v___x_982_;
                        v_isShared_987_ = v_isSharedCheck_994_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_984_);
                        lean_dec(v___x_982_);
                        v___x_986_ = lean_box(0);
                        v_isShared_987_ = v_isSharedCheck_994_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_val_984_) == 1 {
                    v_v_988_ = lean_ctor_get_uint8(v_val_984_, 0 as u32);
                    lean_dec_ref_known(v_val_984_, 0);
                    v___x_989_ = lean_box((v_v_988_) as usize);
                    if v_isShared_987_ == 0 {
                        lean_ctor_set(v___x_986_, 0, v___x_989_);
                        v___x_991_ = v___x_986_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
                        v___x_991_ = v_reuseFailAlloc_992_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_986_);
                    lean_dec(v_val_984_);
                    v___x_993_ = lean_box(0);
                    return v___x_993_;
                }
            }
            2 => {
                return v___x_991_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0___boxed(
    mut v_o_995_: *mut LeanObject,
    mut v_k_996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_997_: *mut LeanObject = core::ptr::null_mut();
    v_res_997_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(
        v_o_995_, v_k_996_,
    );
    lean_dec(v_k_996_);
    lean_dec_ref(v_o_995_);
    return v_res_997_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(
    mut v_x_998_: *mut LeanObject,
    mut v_x_999_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_998_) == 0 {
        if lean_obj_tag(v_x_999_) == 0 {
            let mut v___x_1000_: u8 = 0;
            v___x_1000_ = 1;
            return v___x_1000_;
        } else {
            let mut v___x_1001_: u8 = 0;
            v___x_1001_ = 0;
            return v___x_1001_;
        }
    } else {
        if lean_obj_tag(v_x_999_) == 0 {
            let mut v___x_1002_: u8 = 0;
            v___x_1002_ = 0;
            return v___x_1002_;
        } else {
            let mut v_val_1003_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1004_: u8 = 0;
            v_val_1003_ = lean_ctor_get(v_x_998_, 0);
            v___x_1004_ = (lean_unbox(v_val_1003_) as u8);
            if v___x_1004_ == 0 {
                let mut v_val_1005_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1006_: u8 = 0;
                v_val_1005_ = lean_ctor_get(v_x_999_, 0);
                v___x_1006_ = (lean_unbox(v_val_1005_) as u8);
                if v___x_1006_ == 0 {
                    let mut v___x_1007_: u8 = 0;
                    v___x_1007_ = 1;
                    return v___x_1007_;
                } else {
                    let mut v___x_1008_: u8 = 0;
                    v___x_1008_ = (lean_unbox(v_val_1003_) as u8);
                    return v___x_1008_;
                }
            } else {
                let mut v_val_1009_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1010_: u8 = 0;
                v_val_1009_ = lean_ctor_get(v_x_999_, 0);
                v___x_1010_ = (lean_unbox(v_val_1009_) as u8);
                return v___x_1010_;
            }
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1___boxed(
    mut v_x_1011_: *mut LeanObject,
    mut v_x_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1013_: u8 = 0;
    let mut v_r_1014_: *mut LeanObject = core::ptr::null_mut();
    v_res_1013_ =
        l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(v_x_1011_, v_x_1012_);
    lean_dec(v_x_1012_);
    lean_dec(v_x_1011_);
    v_r_1014_ = lean_box((v_res_1013_) as usize);
    return v_r_1014_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(
    mut v_o_1018_: *mut LeanObject,
    mut v_as_1019_: *mut LeanObject,
    mut v_i_1020_: usize,
    mut v_stop_1021_: usize,
) -> u8 {
    let mut v___x_1022_: u8 = 0;
    let mut v___x_1023_: u8 = 0;
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: u8 = 0;
    let mut v___x_1028_: usize = 0;
    let mut v___x_1029_: usize = 0;
    let mut v___x_1031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1022_ = lean_usize_dec_eq(v_i_1020_, v_stop_1021_);
                if v___x_1022_ == 0 {
                    v___x_1023_ = 1;
                    v___x_1024_ = lean_array_uget_borrowed(v_as_1019_, v_i_1020_);
                    v___x_1025_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_1018_, v___x_1024_);
                    v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0;
                    v___x_1027_ = l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(
                        v___x_1025_,
                        v___x_1026_,
                    );
                    lean_dec(v___x_1025_);
                    if v___x_1027_ == 0 {
                        v___x_1028_ = 1usize;
                        v___x_1029_ = lean_usize_add(v_i_1020_, v___x_1028_);
                        v_i_1020_ = v___x_1029_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1023_;
                    }
                } else {
                    v___x_1031_ = 0;
                    return v___x_1031_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___boxed(
    mut v_o_1032_: *mut LeanObject,
    mut v_as_1033_: *mut LeanObject,
    mut v_i_1034_: *mut LeanObject,
    mut v_stop_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1036_: usize = 0;
    let mut v_stop_boxed_1037_: usize = 0;
    let mut v_res_1038_: u8 = 0;
    let mut v_r_1039_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1036_ = lean_unbox_usize(v_i_1034_);
    lean_dec(v_i_1034_);
    v_stop_boxed_1037_ = lean_unbox_usize(v_stop_1035_);
    lean_dec(v_stop_1035_);
    v_res_1038_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_1032_, v_as_1033_, v_i_boxed_1036_, v_stop_boxed_1037_);
    lean_dec_ref(v_as_1033_);
    lean_dec_ref(v_o_1032_);
    v_r_1039_ = lean_box((v_res_1038_) as usize);
    return v_r_1039_;
}
pub unsafe fn l_Lean_Linter_getLinterValue(
    mut v_opt_1040_: *mut LeanObject,
    mut v_o_1041_: *mut LeanObject,
) -> u8 {
    let mut v_name_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1045_: u8 = 0;
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: u8 = 0;
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    let mut v___x_1052_: u8 = 0;
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: usize = 0;
    let mut v___x_1055_: usize = 0;
    let mut v___x_1056_: u8 = 0;
    let mut v___x_1057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1042_ = lean_ctor_get(v_opt_1040_, 0);
                v_defValue_1043_ = lean_ctor_get(v_opt_1040_, 1);
                v___x_1048_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_1041_, v_opt_1040_);
                v___x_1049_ = lean_unsigned_to_nat(0);
                v___x_1050_ = lean_array_get_size(v___x_1048_);
                v___x_1051_ = lean_nat_dec_lt(v___x_1049_, v___x_1050_);
                if v___x_1051_ == 0 {
                    lean_dec_ref(v___x_1048_);
                    v___x_1052_ = (lean_unbox(v_defValue_1043_) as u8);
                    v___y_1045_ = v___x_1052_;
                    state = 1;
                    continue;
                } else {
                    if v___x_1051_ == 0 {
                        lean_dec_ref(v___x_1048_);
                        v___x_1053_ = (lean_unbox(v_defValue_1043_) as u8);
                        v___y_1045_ = v___x_1053_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1054_ = 0usize;
                        v___x_1055_ = lean_usize_of_nat(v___x_1050_);
                        v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_1041_, v___x_1048_, v___x_1054_, v___x_1055_);
                        lean_dec_ref(v___x_1048_);
                        if v___x_1056_ == 0 {
                            v___x_1057_ = (lean_unbox(v_defValue_1043_) as u8);
                            v___y_1045_ = v___x_1057_;
                            state = 1;
                            continue;
                        } else {
                            v___y_1045_ = v___x_1056_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1046_ = l_Lean_Linter_getLinterAll(v_o_1041_, v___y_1045_);
                v___x_1047_ =
                    l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(
                        v_o_1041_,
                        v_name_1042_,
                        v___x_1046_,
                    );
                return v___x_1047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_getLinterValue___boxed(
    mut v_opt_1058_: *mut LeanObject,
    mut v_o_1059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1060_: u8 = 0;
    let mut v_r_1061_: *mut LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Lean_Linter_getLinterValue(v_opt_1058_, v_o_1059_);
    lean_dec_ref(v_o_1059_);
    lean_dec_ref(v_opt_1058_);
    v_r_1061_ = lean_box((v_res_1060_) as usize);
    return v_r_1061_;
}
pub unsafe fn l_Lean_Linter_getLinterValueExtra(
    mut v_opt_1062_: *mut LeanObject,
    mut v_o_1063_: *mut LeanObject,
) -> u8 {
    let mut v_name_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: u8 = 0;
    let mut v___x_1068_: u8 = 0;
    v_name_1064_ = lean_ctor_get(v_opt_1062_, 0);
    v_defValue_1065_ = lean_ctor_get(v_opt_1062_, 1);
    v___x_1066_ = (lean_unbox(v_defValue_1065_) as u8);
    v___x_1067_ = l_Lean_Linter_getLinterExtra(v_o_1063_, v___x_1066_);
    v___x_1068_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(
        v_o_1063_,
        v_name_1064_,
        v___x_1067_,
    );
    return v___x_1068_;
}
pub unsafe fn l_Lean_Linter_getLinterValueExtra___boxed(
    mut v_opt_1069_: *mut LeanObject,
    mut v_o_1070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1071_: u8 = 0;
    let mut v_r_1072_: *mut LeanObject = core::ptr::null_mut();
    v_res_1071_ = l_Lean_Linter_getLinterValueExtra(v_opt_1069_, v_o_1070_);
    lean_dec_ref(v_o_1070_);
    lean_dec_ref(v_opt_1069_);
    v_r_1072_ = lean_box((v_res_1071_) as usize);
    return v_r_1072_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    v___x_1080_ = l_Lean_Linter_logLint___redArg___closed__0;
    v___x_1081_ = l_Lean_stringToMessageData(v___x_1080_);
    return v___x_1081_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___redArg___closed__3() -> *mut LeanObject {
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    v___x_1083_ = l_Lean_Linter_logLint___redArg___closed__2;
    v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
    return v___x_1084_;
}
pub unsafe fn l_Lean_Linter_logLint___redArg(
    mut v_inst_1085_: *mut LeanObject,
    mut v_inst_1086_: *mut LeanObject,
    mut v_inst_1087_: *mut LeanObject,
    mut v_inst_1088_: *mut LeanObject,
    mut v_linterOption_1089_: *mut LeanObject,
    mut v_stx_1090_: *mut LeanObject,
    mut v_msg_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_disable_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut v_unused_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_1092_ = lean_ctor_get(v_linterOption_1089_, 0);
                v_isSharedCheck_1109_ = (!lean_is_exclusive(v_linterOption_1089_)) as u8;
                if v_isSharedCheck_1109_ == 0 {
                    v_unused_1110_ = lean_ctor_get(v_linterOption_1089_, 1);
                    lean_dec(v_unused_1110_);
                    v___x_1094_ = v_linterOption_1089_;
                    v_isShared_1095_ = v_isSharedCheck_1109_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_name_1092_);
                    lean_dec(v_linterOption_1089_);
                    v___x_1094_ = lean_box(0);
                    v_isShared_1095_ = v_isSharedCheck_1109_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1096_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_logLint___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Linter_logLint___redArg___closed__1_once),
                    _init_l_Lean_Linter_logLint___redArg___closed__1,
                );
                lean_inc(v_name_1092_);
                v___x_1097_ = l_Lean_MessageData_ofName(v_name_1092_);
                if v_isShared_1095_ == 0 {
                    lean_ctor_set_tag(v___x_1094_, 7);
                    lean_ctor_set(v___x_1094_, 1, v___x_1097_);
                    lean_ctor_set(v___x_1094_, 0, v___x_1096_);
                    v___x_1099_ = v___x_1094_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1108_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1096_);
                    lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1097_);
                    v___x_1099_ = v_reuseFailAlloc_1108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1100_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Linter_logLint___redArg___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Linter_logLint___redArg___closed__3_once),
                    _init_l_Lean_Linter_logLint___redArg___closed__3,
                );
                v___x_1101_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1101_, 0, v___x_1099_);
                lean_ctor_set(v___x_1101_, 1, v___x_1100_);
                v_disable_1102_ = l_Lean_MessageData_note(v___x_1101_);
                v___x_1103_ = l_Lean_Linter_linterMessageTag;
                v___x_1104_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1104_, 0, v_msg_1091_);
                lean_ctor_set(v___x_1104_, 1, v_disable_1102_);
                v___x_1105_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1105_, 0, v___x_1103_);
                lean_ctor_set(v___x_1105_, 1, v___x_1104_);
                v___x_1106_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1106_, 0, v_name_1092_);
                lean_ctor_set(v___x_1106_, 1, v___x_1105_);
                v___x_1107_ = l_Lean_logWarningAt___redArg(
                    v_inst_1085_,
                    v_inst_1086_,
                    v_inst_1087_,
                    v_inst_1088_,
                    v_stx_1090_,
                    v___x_1106_,
                );
                return v___x_1107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint(
    mut v_m_1111_: *mut LeanObject,
    mut v_inst_1112_: *mut LeanObject,
    mut v_inst_1113_: *mut LeanObject,
    mut v_inst_1114_: *mut LeanObject,
    mut v_inst_1115_: *mut LeanObject,
    mut v_linterOption_1116_: *mut LeanObject,
    mut v_stx_1117_: *mut LeanObject,
    mut v_msg_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    v___x_1119_ = l_Lean_Linter_logLint___redArg(
        v_inst_1112_,
        v_inst_1113_,
        v_inst_1114_,
        v_inst_1115_,
        v_linterOption_1116_,
        v_stx_1117_,
        v_msg_1118_,
    );
    return v___x_1119_;
}
pub unsafe fn l_Lean_MessageData_isLinterMessage___lam__0(mut v_x_1120_: *mut LeanObject) -> u8 {
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: u8 = 0;
    v___x_1121_ = l_Lean_Linter_linterMessageTag;
    v___x_1122_ = lean_name_eq(v_x_1120_, v___x_1121_);
    return v___x_1122_;
}
pub unsafe fn l_Lean_MessageData_isLinterMessage___lam__0___boxed(
    mut v_x_1123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1124_: u8 = 0;
    let mut v_r_1125_: *mut LeanObject = core::ptr::null_mut();
    v_res_1124_ = l_Lean_MessageData_isLinterMessage___lam__0(v_x_1123_);
    lean_dec(v_x_1123_);
    v_r_1125_ = lean_box((v_res_1124_) as usize);
    return v_r_1125_;
}
pub unsafe fn l_Lean_MessageData_isLinterMessage(mut v_msg_1127_: *mut LeanObject) -> u8 {
    let mut v___f_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: u8 = 0;
    v___f_1128_ = l_Lean_MessageData_isLinterMessage___closed__0;
    v___x_1129_ = l_Lean_MessageData_hasTag(v___f_1128_, v_msg_1127_);
    return v___x_1129_;
}
pub unsafe fn l_Lean_MessageData_isLinterMessage___boxed(
    mut v_msg_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1131_: u8 = 0;
    let mut v_r_1132_: *mut LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Lean_MessageData_isLinterMessage(v_msg_1130_);
    v_r_1132_ = lean_box((v_res_1131_) as usize);
    return v_r_1132_;
}
pub unsafe fn l_Lean_Linter_logLintIf___redArg___lam__0(
    mut v_linterOption_1133_: *mut LeanObject,
    mut v_toApplicative_1134_: *mut LeanObject,
    mut v_inst_1135_: *mut LeanObject,
    mut v_inst_1136_: *mut LeanObject,
    mut v_inst_1137_: *mut LeanObject,
    mut v_inst_1138_: *mut LeanObject,
    mut v_stx_1139_: *mut LeanObject,
    mut v_msg_1140_: *mut LeanObject,
    mut v_____do__lift_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1142_: u8 = 0;
    v___x_1142_ = l_Lean_Linter_getLinterValue(v_linterOption_1133_, v_____do__lift_1141_);
    if v___x_1142_ == 0 {
        let mut v_toPure_1143_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_msg_1140_);
        lean_dec(v_stx_1139_);
        lean_dec(v_inst_1138_);
        lean_dec(v_inst_1137_);
        lean_dec_ref(v_inst_1136_);
        lean_dec_ref(v_inst_1135_);
        lean_dec_ref(v_linterOption_1133_);
        v_toPure_1143_ = lean_ctor_get(v_toApplicative_1134_, 1);
        lean_inc(v_toPure_1143_);
        lean_dec_ref(v_toApplicative_1134_);
        v___x_1144_ = lean_box(0);
        v___x_1145_ = lean_apply_2(v_toPure_1143_, lean_box(0), v___x_1144_);
        return v___x_1145_;
    } else {
        let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_1134_);
        v___x_1146_ = l_Lean_Linter_logLint___redArg(
            v_inst_1135_,
            v_inst_1136_,
            v_inst_1137_,
            v_inst_1138_,
            v_linterOption_1133_,
            v_stx_1139_,
            v_msg_1140_,
        );
        return v___x_1146_;
    }
}
pub unsafe fn l_Lean_Linter_logLintIf___redArg___lam__0___boxed(
    mut v_linterOption_1147_: *mut LeanObject,
    mut v_toApplicative_1148_: *mut LeanObject,
    mut v_inst_1149_: *mut LeanObject,
    mut v_inst_1150_: *mut LeanObject,
    mut v_inst_1151_: *mut LeanObject,
    mut v_inst_1152_: *mut LeanObject,
    mut v_stx_1153_: *mut LeanObject,
    mut v_msg_1154_: *mut LeanObject,
    mut v_____do__lift_1155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1156_: *mut LeanObject = core::ptr::null_mut();
    v_res_1156_ = l_Lean_Linter_logLintIf___redArg___lam__0(
        v_linterOption_1147_,
        v_toApplicative_1148_,
        v_inst_1149_,
        v_inst_1150_,
        v_inst_1151_,
        v_inst_1152_,
        v_stx_1153_,
        v_msg_1154_,
        v_____do__lift_1155_,
    );
    lean_dec_ref(v_____do__lift_1155_);
    return v_res_1156_;
}
pub unsafe fn l_Lean_Linter_logLintIf___redArg(
    mut v_inst_1157_: *mut LeanObject,
    mut v_inst_1158_: *mut LeanObject,
    mut v_inst_1159_: *mut LeanObject,
    mut v_inst_1160_: *mut LeanObject,
    mut v_inst_1161_: *mut LeanObject,
    mut v_linterOption_1162_: *mut LeanObject,
    mut v_stx_1163_: *mut LeanObject,
    mut v_msg_1164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1165_ = lean_ctor_get(v_inst_1157_, 0);
    v_toBind_1166_ = lean_ctor_get(v_inst_1157_, 1);
    lean_inc(v_toBind_1166_);
    lean_inc(v_inst_1160_);
    lean_inc_ref(v_inst_1157_);
    lean_inc_ref(v_toApplicative_1165_);
    v___f_1167_ = lean_alloc_closure(
        l_Lean_Linter_logLintIf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_1167_, 0, v_linterOption_1162_);
    lean_closure_set(v___f_1167_, 1, v_toApplicative_1165_);
    lean_closure_set(v___f_1167_, 2, v_inst_1157_);
    lean_closure_set(v___f_1167_, 3, v_inst_1158_);
    lean_closure_set(v___f_1167_, 4, v_inst_1159_);
    lean_closure_set(v___f_1167_, 5, v_inst_1160_);
    lean_closure_set(v___f_1167_, 6, v_stx_1163_);
    lean_closure_set(v___f_1167_, 7, v_msg_1164_);
    v___x_1168_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_1157_, v_inst_1160_, v_inst_1161_);
    v___x_1169_ = lean_apply_4(
        v_toBind_1166_,
        lean_box(0),
        lean_box(0),
        v___x_1168_,
        v___f_1167_,
    );
    return v___x_1169_;
}
pub unsafe fn l_Lean_Linter_logLintIf(
    mut v_m_1170_: *mut LeanObject,
    mut v_inst_1171_: *mut LeanObject,
    mut v_inst_1172_: *mut LeanObject,
    mut v_inst_1173_: *mut LeanObject,
    mut v_inst_1174_: *mut LeanObject,
    mut v_inst_1175_: *mut LeanObject,
    mut v_linterOption_1176_: *mut LeanObject,
    mut v_stx_1177_: *mut LeanObject,
    mut v_msg_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    v___x_1179_ = l_Lean_Linter_logLintIf___redArg(
        v_inst_1171_,
        v_inst_1172_,
        v_inst_1173_,
        v_inst_1174_,
        v_inst_1175_,
        v_linterOption_1176_,
        v_stx_1177_,
        v_msg_1178_,
    );
    return v___x_1179_;
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___redArg___lam__0(
    mut v_linterOption_1180_: *mut LeanObject,
    mut v_toApplicative_1181_: *mut LeanObject,
    mut v_inst_1182_: *mut LeanObject,
    mut v_inst_1183_: *mut LeanObject,
    mut v_inst_1184_: *mut LeanObject,
    mut v_inst_1185_: *mut LeanObject,
    mut v_stx_1186_: *mut LeanObject,
    mut v_msg_1187_: *mut LeanObject,
    mut v_____do__lift_1188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1189_: u8 = 0;
    v___x_1189_ = l_Lean_Linter_getLinterValueExtra(v_linterOption_1180_, v_____do__lift_1188_);
    if v___x_1189_ == 0 {
        let mut v_toPure_1190_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_msg_1187_);
        lean_dec(v_stx_1186_);
        lean_dec(v_inst_1185_);
        lean_dec(v_inst_1184_);
        lean_dec_ref(v_inst_1183_);
        lean_dec_ref(v_inst_1182_);
        lean_dec_ref(v_linterOption_1180_);
        v_toPure_1190_ = lean_ctor_get(v_toApplicative_1181_, 1);
        lean_inc(v_toPure_1190_);
        lean_dec_ref(v_toApplicative_1181_);
        v___x_1191_ = lean_box(0);
        v___x_1192_ = lean_apply_2(v_toPure_1190_, lean_box(0), v___x_1191_);
        return v___x_1192_;
    } else {
        let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_1181_);
        v___x_1193_ = l_Lean_Linter_logLint___redArg(
            v_inst_1182_,
            v_inst_1183_,
            v_inst_1184_,
            v_inst_1185_,
            v_linterOption_1180_,
            v_stx_1186_,
            v_msg_1187_,
        );
        return v___x_1193_;
    }
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___redArg___lam__0___boxed(
    mut v_linterOption_1194_: *mut LeanObject,
    mut v_toApplicative_1195_: *mut LeanObject,
    mut v_inst_1196_: *mut LeanObject,
    mut v_inst_1197_: *mut LeanObject,
    mut v_inst_1198_: *mut LeanObject,
    mut v_inst_1199_: *mut LeanObject,
    mut v_stx_1200_: *mut LeanObject,
    mut v_msg_1201_: *mut LeanObject,
    mut v_____do__lift_1202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1203_: *mut LeanObject = core::ptr::null_mut();
    v_res_1203_ = l_Lean_Linter_logLintIfExtra___redArg___lam__0(
        v_linterOption_1194_,
        v_toApplicative_1195_,
        v_inst_1196_,
        v_inst_1197_,
        v_inst_1198_,
        v_inst_1199_,
        v_stx_1200_,
        v_msg_1201_,
        v_____do__lift_1202_,
    );
    lean_dec_ref(v_____do__lift_1202_);
    return v_res_1203_;
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___redArg(
    mut v_inst_1204_: *mut LeanObject,
    mut v_inst_1205_: *mut LeanObject,
    mut v_inst_1206_: *mut LeanObject,
    mut v_inst_1207_: *mut LeanObject,
    mut v_inst_1208_: *mut LeanObject,
    mut v_linterOption_1209_: *mut LeanObject,
    mut v_stx_1210_: *mut LeanObject,
    mut v_msg_1211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1212_ = lean_ctor_get(v_inst_1204_, 0);
    v_toBind_1213_ = lean_ctor_get(v_inst_1204_, 1);
    lean_inc(v_toBind_1213_);
    lean_inc(v_inst_1207_);
    lean_inc_ref(v_inst_1204_);
    lean_inc_ref(v_toApplicative_1212_);
    v___f_1214_ = lean_alloc_closure(
        l_Lean_Linter_logLintIfExtra___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_1214_, 0, v_linterOption_1209_);
    lean_closure_set(v___f_1214_, 1, v_toApplicative_1212_);
    lean_closure_set(v___f_1214_, 2, v_inst_1204_);
    lean_closure_set(v___f_1214_, 3, v_inst_1205_);
    lean_closure_set(v___f_1214_, 4, v_inst_1206_);
    lean_closure_set(v___f_1214_, 5, v_inst_1207_);
    lean_closure_set(v___f_1214_, 6, v_stx_1210_);
    lean_closure_set(v___f_1214_, 7, v_msg_1211_);
    v___x_1215_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_1204_, v_inst_1207_, v_inst_1208_);
    v___x_1216_ = lean_apply_4(
        v_toBind_1213_,
        lean_box(0),
        lean_box(0),
        v___x_1215_,
        v___f_1214_,
    );
    return v___x_1216_;
}
pub unsafe fn l_Lean_Linter_logLintIfExtra(
    mut v_m_1217_: *mut LeanObject,
    mut v_inst_1218_: *mut LeanObject,
    mut v_inst_1219_: *mut LeanObject,
    mut v_inst_1220_: *mut LeanObject,
    mut v_inst_1221_: *mut LeanObject,
    mut v_inst_1222_: *mut LeanObject,
    mut v_linterOption_1223_: *mut LeanObject,
    mut v_stx_1224_: *mut LeanObject,
    mut v_msg_1225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    v___x_1226_ = l_Lean_Linter_logLintIfExtra___redArg(
        v_inst_1218_,
        v_inst_1219_,
        v_inst_1220_,
        v_inst_1221_,
        v_inst_1222_,
        v_linterOption_1223_,
        v_stx_1224_,
        v_msg_1225_,
    );
    return v___x_1226_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Init(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_MonadEnv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Linter_instEmptyCollectionLinterSets___aux__1 =
        _init_l_Lean_Linter_instEmptyCollectionLinterSets___aux__1();
    lean_mark_persistent(l_Lean_Linter_instEmptyCollectionLinterSets___aux__1);
    l_Lean_Linter_instEmptyCollectionLinterSets =
        _init_l_Lean_Linter_instEmptyCollectionLinterSets();
    lean_mark_persistent(l_Lean_Linter_instEmptyCollectionLinterSets);
    l_Lean_Linter_instInhabitedLinterSets___aux__1 =
        _init_l_Lean_Linter_instInhabitedLinterSets___aux__1();
    lean_mark_persistent(l_Lean_Linter_instInhabitedLinterSets___aux__1);
    l_Lean_Linter_instInhabitedLinterSets = _init_l_Lean_Linter_instInhabitedLinterSets();
    lean_mark_persistent(l_Lean_Linter_instInhabitedLinterSets);
    res = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1102181608____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linterSetsExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_linterSetsExt);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_all = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_linter_all);
    lean_dec_ref(res);
    res = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_linter_extra = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Linter_linter_extra);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Init(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Linter_Init(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_MonadEnv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Linter_Init(builtin);
}
