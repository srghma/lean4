// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.Opaque
// Imports: Lean.ScopedEnvExtension Lean.ReducibilityAttrs
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1,
};
use crate::r#gen::Lean::Attributes::l_Lean_registerBuiltinAttribute;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofConstName, l_Lean_stringToMessageData};
use crate::r#gen::Lean::ReducibilityAttrs::{
    initialize_Lean_ReducibilityAttrs, lean_get_reducibility_status,
    runtime_initialize_Lean_ReducibilityAttrs,
};
use crate::r#gen::Lean::ScopedEnvExtension::{
    initialize_Lean_ScopedEnvExtension, l_Lean_ScopedEnvExtension_addCore___redArg,
    l_Lean_ScopedEnvExtension_getState___redArg, l_Lean_ScopedEnvExtension_modifyState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg, runtime_initialize_Lean_ScopedEnvExtension,
};
use crate::r#gen::Std::Data::HashSet::Basic::l_Std_HashSet_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unsigned_to_nat,
};
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0: u64 = 0;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [99, 98, 118, 79, 112, 97, 113, 117, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value) as *mut LeanObject,3589185701406341147 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanStringObject<69> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 69, m_capacity: 69, m_length: 68, m_data: [96, 64, 91, 99, 98, 118, 95, 111, 112, 97, 113, 117, 101, 93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 97, 112, 112, 108, 105, 101, 100, 32, 116, 111, 32, 97, 32, 96, 64, 91, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 58, 32, 96, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanStringObject<52> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [96, 32, 105, 115, 32, 114, 101, 100, 117, 99, 105, 98, 108, 101, 44, 32, 115, 111, 32, 105, 116, 32, 105, 115, 32, 117, 110, 102, 111, 108, 100, 101, 100, 32, 98, 101, 102, 111, 114, 101, 32, 96, 99, 98, 118, 96, 32, 114, 117, 110, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [99, 98, 118, 79, 112, 97, 113, 117, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject,8927619598210679338 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 98, 118, 95, 111, 112, 97, 113, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject,3278606391115206441 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanStringObject<66> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 66, m_capacity: 66, m_length: 65, m_data: [77, 97, 114, 107, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32, 117, 110, 102, 111, 108, 100, 101, 100, 32, 98, 121, 32, 116, 104, 101, 32, 96, 99, 98, 118, 96, 32, 116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject,1 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_(
    mut v_x_631_: *mut LeanObject,
    mut v_a_632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    v___x_633_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_633_, 0, v_a_632_);
    lean_inc_ref_n(v___x_633_, 2);
    v___x_634_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_634_, 0, v___x_633_);
    lean_ctor_set(v___x_634_, 1, v___x_633_);
    lean_ctor_set(v___x_634_, 2, v___x_633_);
    return v___x_634_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2____boxed(
    mut v_x_635_: *mut LeanObject,
    mut v_a_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_637_: *mut LeanObject = core::ptr::null_mut();
    v_res_637_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_(v_x_635_, v_a_636_);
    lean_dec_ref(v_x_635_);
    return v_res_637_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_a_638_: *mut LeanObject,
    mut v_x_639_: *mut LeanObject,
) -> u8 {
    let mut v___x_640_: u8 = 0;
    let mut v_key_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_639_) == 0 {
                    v___x_640_ = 0;
                    return v___x_640_;
                } else {
                    v_key_641_ = lean_ctor_get(v_x_639_, 0);
                    v_tail_642_ = lean_ctor_get(v_x_639_, 2);
                    v___x_643_ = lean_name_eq(v_key_641_, v_a_638_);
                    if v___x_643_ == 0 {
                        v_x_639_ = v_tail_642_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_643_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_a_645_: *mut LeanObject,
    mut v_x_646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_647_: u8 = 0;
    let mut v_r_648_: *mut LeanObject = core::ptr::null_mut();
    v_res_647_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_645_, v_x_646_);
    lean_dec(v_x_646_);
    lean_dec(v_a_645_);
    v_r_648_ = lean_box((v_res_647_) as usize);
    return v_r_648_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: u64 = 0;
    v___x_649_ = lean_unsigned_to_nat(1723);
    v___x_650_ = lean_uint64_of_nat(v___x_649_);
    return v___x_650_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_651_: *mut LeanObject,
    mut v_x_652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_658_: u8 = 0;
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_661_: u64 = 0;
    let mut v___x_662_: u64 = 0;
    let mut v___x_663_: u64 = 0;
    let mut v_fold_664_: u64 = 0;
    let mut v___x_665_: u64 = 0;
    let mut v___x_666_: u64 = 0;
    let mut v___x_667_: u64 = 0;
    let mut v___x_668_: usize = 0;
    let mut v___x_669_: usize = 0;
    let mut v___x_670_: usize = 0;
    let mut v___x_671_: usize = 0;
    let mut v___x_672_: usize = 0;
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: u64 = 0;
    let mut v_hash_680_: u64 = 0;
    let mut v_isSharedCheck_681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_652_) == 0 {
                    return v_x_651_;
                } else {
                    v_key_653_ = lean_ctor_get(v_x_652_, 0);
                    v_value_654_ = lean_ctor_get(v_x_652_, 1);
                    v_tail_655_ = lean_ctor_get(v_x_652_, 2);
                    v_isSharedCheck_681_ = (!lean_is_exclusive(v_x_652_)) as u8;
                    if v_isSharedCheck_681_ == 0 {
                        v___x_657_ = v_x_652_;
                        v_isShared_658_ = v_isSharedCheck_681_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_655_);
                        lean_inc(v_value_654_);
                        lean_inc(v_key_653_);
                        lean_dec(v_x_652_);
                        v___x_657_ = lean_box(0);
                        v_isShared_658_ = v_isSharedCheck_681_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_659_ = lean_array_get_size(v_x_651_);
                if lean_obj_tag(v_key_653_) == 0 {
                    v___x_679_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_661_ = v___x_679_;
                    state = 2;
                    continue;
                } else {
                    v_hash_680_ = lean_ctor_get_uint64(
                        v_key_653_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_661_ = v_hash_680_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_662_ = 32u64;
                v___x_663_ = lean_uint64_shift_right(v___y_661_, v___x_662_);
                v_fold_664_ = lean_uint64_xor(v___y_661_, v___x_663_);
                v___x_665_ = 16u64;
                v___x_666_ = lean_uint64_shift_right(v_fold_664_, v___x_665_);
                v___x_667_ = lean_uint64_xor(v_fold_664_, v___x_666_);
                v___x_668_ = lean_uint64_to_usize(v___x_667_);
                v___x_669_ = lean_usize_of_nat(v___x_659_);
                v___x_670_ = 1usize;
                v___x_671_ = lean_usize_sub(v___x_669_, v___x_670_);
                v___x_672_ = lean_usize_land(v___x_668_, v___x_671_);
                v___x_673_ = lean_array_uget_borrowed(v_x_651_, v___x_672_);
                lean_inc(v___x_673_);
                if v_isShared_658_ == 0 {
                    lean_ctor_set(v___x_657_, 2, v___x_673_);
                    v___x_675_ = v___x_657_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_678_, 0, v_key_653_);
                    lean_ctor_set(v_reuseFailAlloc_678_, 1, v_value_654_);
                    lean_ctor_set(v_reuseFailAlloc_678_, 2, v___x_673_);
                    v___x_675_ = v_reuseFailAlloc_678_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_676_ = lean_array_uset(v_x_651_, v___x_672_, v___x_675_);
                v_x_651_ = v___x_676_;
                v_x_652_ = v_tail_655_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(
    mut v_i_682_: *mut LeanObject,
    mut v_source_683_: *mut LeanObject,
    mut v_target_684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: u8 = 0;
    let mut v_es_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_685_ = lean_array_get_size(v_source_683_);
                v___x_686_ = lean_nat_dec_lt(v_i_682_, v___x_685_);
                if v___x_686_ == 0 {
                    lean_dec_ref(v_source_683_);
                    lean_dec(v_i_682_);
                    return v_target_684_;
                } else {
                    v_es_687_ = lean_array_fget(v_source_683_, v_i_682_);
                    v___x_688_ = lean_box(0);
                    v_source_689_ = lean_array_fset(v_source_683_, v_i_682_, v___x_688_);
                    v_target_690_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_684_, v_es_687_);
                    v___x_691_ = lean_unsigned_to_nat(1);
                    v___x_692_ = lean_nat_add(v_i_682_, v___x_691_);
                    lean_dec(v_i_682_);
                    v_i_682_ = v___x_692_;
                    v_source_683_ = v_source_689_;
                    v_target_684_ = v_target_690_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1___redArg(
    mut v_data_694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    v___x_695_ = lean_array_get_size(v_data_694_);
    v___x_696_ = lean_unsigned_to_nat(2);
    v_nbuckets_697_ = lean_nat_mul(v___x_695_, v___x_696_);
    v___x_698_ = lean_unsigned_to_nat(0);
    v___x_699_ = lean_box(0);
    v___x_700_ = lean_mk_array(v_nbuckets_697_, v___x_699_);
    v___x_701_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_698_, v_data_694_, v___x_700_);
    return v___x_701_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0___redArg(
    mut v_m_702_: *mut LeanObject,
    mut v_a_703_: *mut LeanObject,
    mut v_b_704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_709_: u64 = 0;
    let mut v___x_710_: u64 = 0;
    let mut v___x_711_: u64 = 0;
    let mut v_fold_712_: u64 = 0;
    let mut v___x_713_: u64 = 0;
    let mut v___x_714_: u64 = 0;
    let mut v___x_715_: u64 = 0;
    let mut v___x_716_: usize = 0;
    let mut v___x_717_: usize = 0;
    let mut v___x_718_: usize = 0;
    let mut v___x_719_: usize = 0;
    let mut v___x_720_: usize = 0;
    let mut v_bkt_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_725_: u8 = 0;
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: u8 = 0;
    let mut v_val_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_743_: u8 = 0;
    let mut v_unused_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: u64 = 0;
    let mut v_hash_747_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_705_ = lean_ctor_get(v_m_702_, 0);
                v_buckets_706_ = lean_ctor_get(v_m_702_, 1);
                v___x_707_ = lean_array_get_size(v_buckets_706_);
                if lean_obj_tag(v_a_703_) == 0 {
                    v___x_746_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_709_ = v___x_746_;
                    state = 1;
                    continue;
                } else {
                    v_hash_747_ = lean_ctor_get_uint64(
                        v_a_703_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_709_ = v_hash_747_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_710_ = 32u64;
                v___x_711_ = lean_uint64_shift_right(v___y_709_, v___x_710_);
                v_fold_712_ = lean_uint64_xor(v___y_709_, v___x_711_);
                v___x_713_ = 16u64;
                v___x_714_ = lean_uint64_shift_right(v_fold_712_, v___x_713_);
                v___x_715_ = lean_uint64_xor(v_fold_712_, v___x_714_);
                v___x_716_ = lean_uint64_to_usize(v___x_715_);
                v___x_717_ = lean_usize_of_nat(v___x_707_);
                v___x_718_ = 1usize;
                v___x_719_ = lean_usize_sub(v___x_717_, v___x_718_);
                v___x_720_ = lean_usize_land(v___x_716_, v___x_719_);
                v_bkt_721_ = lean_array_uget_borrowed(v_buckets_706_, v___x_720_);
                v___x_722_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_703_, v_bkt_721_);
                if v___x_722_ == 0 {
                    lean_inc_ref(v_buckets_706_);
                    lean_inc(v_size_705_);
                    v_isSharedCheck_743_ = (!lean_is_exclusive(v_m_702_)) as u8;
                    if v_isSharedCheck_743_ == 0 {
                        v_unused_744_ = lean_ctor_get(v_m_702_, 1);
                        lean_dec(v_unused_744_);
                        v_unused_745_ = lean_ctor_get(v_m_702_, 0);
                        lean_dec(v_unused_745_);
                        v___x_724_ = v_m_702_;
                        v_isShared_725_ = v_isSharedCheck_743_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_702_);
                        v___x_724_ = lean_box(0);
                        v_isShared_725_ = v_isSharedCheck_743_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_704_);
                    lean_dec(v_a_703_);
                    return v_m_702_;
                }
            }
            2 => {
                v___x_726_ = lean_unsigned_to_nat(1);
                v_size_x27_727_ = lean_nat_add(v_size_705_, v___x_726_);
                lean_dec(v_size_705_);
                lean_inc(v_bkt_721_);
                v___x_728_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_728_, 0, v_a_703_);
                lean_ctor_set(v___x_728_, 1, v_b_704_);
                lean_ctor_set(v___x_728_, 2, v_bkt_721_);
                v_buckets_x27_729_ = lean_array_uset(v_buckets_706_, v___x_720_, v___x_728_);
                v___x_730_ = lean_unsigned_to_nat(4);
                v___x_731_ = lean_nat_mul(v_size_x27_727_, v___x_730_);
                v___x_732_ = lean_unsigned_to_nat(3);
                v___x_733_ = lean_nat_div(v___x_731_, v___x_732_);
                lean_dec(v___x_731_);
                v___x_734_ = lean_array_get_size(v_buckets_x27_729_);
                v___x_735_ = lean_nat_dec_le(v___x_733_, v___x_734_);
                lean_dec(v___x_733_);
                if v___x_735_ == 0 {
                    v_val_736_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_729_);
                    if v_isShared_725_ == 0 {
                        lean_ctor_set(v___x_724_, 1, v_val_736_);
                        lean_ctor_set(v___x_724_, 0, v_size_x27_727_);
                        v___x_738_ = v___x_724_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_739_, 0, v_size_x27_727_);
                        lean_ctor_set(v_reuseFailAlloc_739_, 1, v_val_736_);
                        v___x_738_ = v_reuseFailAlloc_739_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_725_ == 0 {
                        lean_ctor_set(v___x_724_, 1, v_buckets_x27_729_);
                        lean_ctor_set(v___x_724_, 0, v_size_x27_727_);
                        v___x_741_ = v___x_724_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_742_, 0, v_size_x27_727_);
                        lean_ctor_set(v_reuseFailAlloc_742_, 1, v_buckets_x27_729_);
                        v___x_741_ = v_reuseFailAlloc_742_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_738_;
            }
            4 => {
                return v___x_741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_(
    mut v_s_748_: *mut LeanObject,
    mut v_n_749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    v___x_750_ = lean_box(0);
    v___x_751_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0___redArg(v_s_748_, v_n_749_, v___x_750_);
    return v___x_751_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_(
    mut v___y_752_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_752_);
    return v___y_752_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2____boxed(
    mut v___y_753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_754_: *mut LeanObject = core::ptr::null_mut();
    v_res_754_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_(v___y_753_);
    lean_dec_ref(v___y_753_);
    return v_res_754_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    v___x_761_ = lean_box(0);
    v___x_762_ = lean_unsigned_to_nat(16);
    v___x_763_ = lean_mk_array(v___x_762_, v___x_761_);
    return v___x_763_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    v___x_764_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_);
    v___x_765_ = lean_unsigned_to_nat(0);
    v___x_766_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_766_, 0, v___x_765_);
    lean_ctor_set(v___x_766_, 1, v___x_764_);
    return v___x_766_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___f_767_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_;
    v___f_768_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_;
    v___x_769_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_);
    v___f_770_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_;
    v___x_771_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_;
    v___x_772_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_772_, 0, v___x_771_);
    lean_ctor_set(v___x_772_, 1, v___f_770_);
    lean_ctor_set(v___x_772_, 2, v___x_769_);
    lean_ctor_set(v___x_772_, 3, v___f_768_);
    lean_ctor_set(v___x_772_, 4, v___f_767_);
    return v___x_772_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    v___x_774_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_);
    v___x_775_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_774_);
    return v___x_775_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2____boxed(
    mut v_a_776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_777_: *mut LeanObject = core::ptr::null_mut();
    v_res_777_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_();
    return v_res_777_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_778_: *mut LeanObject,
    mut v_m_779_: *mut LeanObject,
    mut v_a_780_: *mut LeanObject,
    mut v_b_781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    v___x_782_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0___redArg(v_m_779_, v_a_780_, v_b_781_);
    return v___x_782_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b2_783_: *mut LeanObject,
    mut v_a_784_: *mut LeanObject,
    mut v_x_785_: *mut LeanObject,
) -> u8 {
    let mut v___x_786_: u8 = 0;
    v___x_786_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_784_, v_x_785_);
    return v___x_786_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b2_787_: *mut LeanObject,
    mut v_a_788_: *mut LeanObject,
    mut v_x_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_790_: u8 = 0;
    let mut v_r_791_: *mut LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_787_, v_a_788_, v_x_789_);
    lean_dec(v_x_789_);
    lean_dec(v_a_788_);
    v_r_791_ = lean_box((v_res_790_) as usize);
    return v_r_791_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1(
    mut v_00_u03b2_792_: *mut LeanObject,
    mut v_data_793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    v___x_794_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_793_);
    return v___x_794_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2(
    mut v_00_u03b2_795_: *mut LeanObject,
    mut v_i_796_: *mut LeanObject,
    mut v_source_797_: *mut LeanObject,
    mut v_target_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_799_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_796_, v_source_797_, v_target_798_);
    return v___x_799_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_800_: *mut LeanObject,
    mut v_x_801_: *mut LeanObject,
    mut v_x_802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    v___x_803_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_801_, v_x_802_);
    return v___x_803_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    v___x_804_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_804_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    v___x_805_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__0);
    v___x_806_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_806_, 0, v___x_805_);
    return v___x_806_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    v___x_807_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__1);
    v___x_808_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_808_, 0, v___x_807_);
    lean_ctor_set(v___x_808_, 1, v___x_807_);
    return v___x_808_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg(
    mut v_ext_809_: *mut LeanObject,
    mut v_b_810_: *mut LeanObject,
    mut v_kind_811_: u8,
    mut v___y_812_: *mut LeanObject,
    mut v___y_813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currNamespace_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_827_: u8 = 0;
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_836_: u8 = 0;
    let mut v_unused_837_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_815_ = lean_ctor_get(v___y_812_, 6);
                v___x_816_ = lean_st_ref_take(v___y_813_);
                v_env_817_ = lean_ctor_get(v___x_816_, 0);
                v_nextMacroScope_818_ = lean_ctor_get(v___x_816_, 1);
                v_ngen_819_ = lean_ctor_get(v___x_816_, 2);
                v_auxDeclNGen_820_ = lean_ctor_get(v___x_816_, 3);
                v_traceState_821_ = lean_ctor_get(v___x_816_, 4);
                v_messages_822_ = lean_ctor_get(v___x_816_, 6);
                v_infoState_823_ = lean_ctor_get(v___x_816_, 7);
                v_snapshotTasks_824_ = lean_ctor_get(v___x_816_, 8);
                v_isSharedCheck_836_ = (!lean_is_exclusive(v___x_816_)) as u8;
                if v_isSharedCheck_836_ == 0 {
                    v_unused_837_ = lean_ctor_get(v___x_816_, 5);
                    lean_dec(v_unused_837_);
                    v___x_826_ = v___x_816_;
                    v_isShared_827_ = v_isSharedCheck_836_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_824_);
                    lean_inc(v_infoState_823_);
                    lean_inc(v_messages_822_);
                    lean_inc(v_traceState_821_);
                    lean_inc(v_auxDeclNGen_820_);
                    lean_inc(v_ngen_819_);
                    lean_inc(v_nextMacroScope_818_);
                    lean_inc(v_env_817_);
                    lean_dec(v___x_816_);
                    v___x_826_ = lean_box(0);
                    v_isShared_827_ = v_isSharedCheck_836_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_currNamespace_815_);
                v___x_828_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_817_,
                    v_ext_809_,
                    v_b_810_,
                    v_kind_811_,
                    v_currNamespace_815_,
                );
                v___x_829_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__2);
                if v_isShared_827_ == 0 {
                    lean_ctor_set(v___x_826_, 5, v___x_829_);
                    lean_ctor_set(v___x_826_, 0, v___x_828_);
                    v___x_831_ = v___x_826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_828_);
                    lean_ctor_set(v_reuseFailAlloc_835_, 1, v_nextMacroScope_818_);
                    lean_ctor_set(v_reuseFailAlloc_835_, 2, v_ngen_819_);
                    lean_ctor_set(v_reuseFailAlloc_835_, 3, v_auxDeclNGen_820_);
                    lean_ctor_set(v_reuseFailAlloc_835_, 4, v_traceState_821_);
                    lean_ctor_set(v_reuseFailAlloc_835_, 5, v___x_829_);
                    lean_ctor_set(v_reuseFailAlloc_835_, 6, v_messages_822_);
                    lean_ctor_set(v_reuseFailAlloc_835_, 7, v_infoState_823_);
                    lean_ctor_set(v_reuseFailAlloc_835_, 8, v_snapshotTasks_824_);
                    v___x_831_ = v_reuseFailAlloc_835_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_832_ = lean_st_ref_set(v___y_813_, v___x_831_);
                v___x_833_ = lean_box(0);
                v___x_834_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_834_, 0, v___x_833_);
                return v___x_834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_ext_838_: *mut LeanObject,
    mut v_b_839_: *mut LeanObject,
    mut v_kind_840_: *mut LeanObject,
    mut v___y_841_: *mut LeanObject,
    mut v___y_842_: *mut LeanObject,
    mut v___y_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_844_: u8 = 0;
    let mut v_res_845_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_844_ = (lean_unbox(v_kind_840_) as u8);
    v_res_845_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg(v_ext_838_, v_b_839_, v_kind_boxed_844_, v___y_841_, v___y_842_);
    lean_dec(v___y_842_);
    lean_dec_ref(v___y_841_);
    return v_res_845_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_846_: *mut LeanObject,
    mut v_00_u03b2_847_: *mut LeanObject,
    mut v_00_u03c3_848_: *mut LeanObject,
    mut v_ext_849_: *mut LeanObject,
    mut v_b_850_: *mut LeanObject,
    mut v_kind_851_: u8,
    mut v___y_852_: *mut LeanObject,
    mut v___y_853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    v___x_855_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg(v_ext_849_, v_b_850_, v_kind_851_, v___y_852_, v___y_853_);
    return v___x_855_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_856_: *mut LeanObject,
    mut v_00_u03b2_857_: *mut LeanObject,
    mut v_00_u03c3_858_: *mut LeanObject,
    mut v_ext_859_: *mut LeanObject,
    mut v_b_860_: *mut LeanObject,
    mut v_kind_861_: *mut LeanObject,
    mut v___y_862_: *mut LeanObject,
    mut v___y_863_: *mut LeanObject,
    mut v___y_864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_865_: u8 = 0;
    let mut v_res_866_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_865_ = (lean_unbox(v_kind_861_) as u8);
    v_res_866_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0(v_00_u03b1_856_, v_00_u03b2_857_, v_00_u03c3_858_, v_ext_859_, v_b_860_, v_kind_boxed_865_, v___y_862_, v___y_863_);
    lean_dec(v___y_863_);
    lean_dec_ref(v___y_862_);
    return v_res_866_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    v___x_867_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_867_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    v___x_868_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__0);
    v___x_869_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_869_, 0, v___x_868_);
    return v___x_869_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    v___x_870_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__1);
    v___x_871_ = lean_unsigned_to_nat(0);
    v___x_872_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_872_, 0, v___x_871_);
    lean_ctor_set(v___x_872_, 1, v___x_871_);
    lean_ctor_set(v___x_872_, 2, v___x_871_);
    lean_ctor_set(v___x_872_, 3, v___x_871_);
    lean_ctor_set(v___x_872_, 4, v___x_870_);
    lean_ctor_set(v___x_872_, 5, v___x_870_);
    lean_ctor_set(v___x_872_, 6, v___x_870_);
    lean_ctor_set(v___x_872_, 7, v___x_870_);
    lean_ctor_set(v___x_872_, 8, v___x_870_);
    lean_ctor_set(v___x_872_, 9, v___x_870_);
    return v___x_872_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    v___x_873_ = lean_unsigned_to_nat(32);
    v___x_874_ = lean_mk_empty_array_with_capacity(v___x_873_);
    v___x_875_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_875_, 0, v___x_874_);
    return v___x_875_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__4()
-> *mut LeanObject {
    let mut v___x_876_: usize = 0;
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    v___x_876_ = 5usize;
    v___x_877_ = lean_unsigned_to_nat(0);
    v___x_878_ = lean_unsigned_to_nat(32);
    v___x_879_ = lean_mk_empty_array_with_capacity(v___x_878_);
    v___x_880_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__3);
    v___x_881_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_881_, 0, v___x_880_);
    lean_ctor_set(v___x_881_, 1, v___x_879_);
    lean_ctor_set(v___x_881_, 2, v___x_877_);
    lean_ctor_set(v___x_881_, 3, v___x_877_);
    lean_ctor_set_usize(v___x_881_, 4, v___x_876_);
    return v___x_881_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__5()
-> *mut LeanObject {
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    v___x_882_ = lean_box(1);
    v___x_883_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__4);
    v___x_884_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__1);
    v___x_885_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_885_, 0, v___x_884_);
    lean_ctor_set(v___x_885_, 1, v___x_883_);
    lean_ctor_set(v___x_885_, 2, v___x_882_);
    return v___x_885_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3(
    mut v_msgData_886_: *mut LeanObject,
    mut v___y_887_: *mut LeanObject,
    mut v___y_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    v___x_890_ = lean_st_ref_get(v___y_888_);
    v_env_891_ = lean_ctor_get(v___x_890_, 0);
    lean_inc_ref(v_env_891_);
    lean_dec(v___x_890_);
    v_options_892_ = lean_ctor_get(v___y_887_, 2);
    v___x_893_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__2);
    v___x_894_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___closed__5);
    lean_inc_ref(v_options_892_);
    v___x_895_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_895_, 0, v_env_891_);
    lean_ctor_set(v___x_895_, 1, v___x_893_);
    lean_ctor_set(v___x_895_, 2, v___x_894_);
    lean_ctor_set(v___x_895_, 3, v_options_892_);
    v___x_896_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_896_, 0, v___x_895_);
    lean_ctor_set(v___x_896_, 1, v_msgData_886_);
    v___x_897_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_897_, 0, v___x_896_);
    return v___x_897_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3___boxed(
    mut v_msgData_898_: *mut LeanObject,
    mut v___y_899_: *mut LeanObject,
    mut v___y_900_: *mut LeanObject,
    mut v___y_901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_902_: *mut LeanObject = core::ptr::null_mut();
    v_res_902_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3(v_msgData_898_, v___y_899_, v___y_900_);
    lean_dec(v___y_900_);
    lean_dec_ref(v___y_899_);
    return v_res_902_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2___redArg(
    mut v_msg_903_: *mut LeanObject,
    mut v___y_904_: *mut LeanObject,
    mut v___y_905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_912_: u8 = 0;
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_907_ = lean_ctor_get(v___y_904_, 5);
                v___x_908_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2_spec__3(v_msg_903_, v___y_904_, v___y_905_);
                v_a_909_ = lean_ctor_get(v___x_908_, 0);
                v_isSharedCheck_917_ = (!lean_is_exclusive(v___x_908_)) as u8;
                if v_isSharedCheck_917_ == 0 {
                    v___x_911_ = v___x_908_;
                    v_isShared_912_ = v_isSharedCheck_917_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_909_);
                    lean_dec(v___x_908_);
                    v___x_911_ = lean_box(0);
                    v_isShared_912_ = v_isSharedCheck_917_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_907_);
                v___x_913_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_913_, 0, v_ref_907_);
                lean_ctor_set(v___x_913_, 1, v_a_909_);
                if v_isShared_912_ == 0 {
                    lean_ctor_set_tag(v___x_911_, 1);
                    lean_ctor_set(v___x_911_, 0, v___x_913_);
                    v___x_915_ = v___x_911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
                    v___x_915_ = v_reuseFailAlloc_916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_915_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_msg_918_: *mut LeanObject,
    mut v___y_919_: *mut LeanObject,
    mut v___y_920_: *mut LeanObject,
    mut v___y_921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_922_: *mut LeanObject = core::ptr::null_mut();
    v_res_922_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2___redArg(v_msg_918_, v___y_919_, v___y_920_);
    lean_dec(v___y_920_);
    lean_dec_ref(v___y_919_);
    return v_res_922_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1_spec__1___redArg(
    mut v_declName_923_: *mut LeanObject,
    mut v___y_924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: u8 = 0;
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    v___x_926_ = lean_st_ref_get(v___y_924_);
    v_env_927_ = lean_ctor_get(v___x_926_, 0);
    lean_inc_ref(v_env_927_);
    lean_dec(v___x_926_);
    v___x_928_ = lean_get_reducibility_status(v_env_927_, v_declName_923_);
    v___x_929_ = lean_box((v___x_928_) as usize);
    v___x_930_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_930_, 0, v___x_929_);
    return v___x_930_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1_spec__1___redArg___boxed(
    mut v_declName_931_: *mut LeanObject,
    mut v___y_932_: *mut LeanObject,
    mut v___y_933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_934_: *mut LeanObject = core::ptr::null_mut();
    v_res_934_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1_spec__1___redArg(v_declName_931_, v___y_932_);
    lean_dec(v___y_932_);
    return v_res_934_;
}
pub unsafe fn l_Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1(
    mut v_declName_935_: *mut LeanObject,
    mut v___y_936_: *mut LeanObject,
    mut v___y_937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_943_: u8 = 0;
    let mut v___x_944_: u8 = 0;
    let mut v___x_945_: u8 = 0;
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: u8 = 0;
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_955_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_939_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1_spec__1___redArg(v_declName_935_, v___y_937_);
                v_a_940_ = lean_ctor_get(v___x_939_, 0);
                v_isSharedCheck_955_ = (!lean_is_exclusive(v___x_939_)) as u8;
                if v_isSharedCheck_955_ == 0 {
                    v___x_942_ = v___x_939_;
                    v_isShared_943_ = v_isSharedCheck_955_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_940_);
                    lean_dec(v___x_939_);
                    v___x_942_ = lean_box(0);
                    v_isShared_943_ = v_isSharedCheck_955_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_944_ = (lean_unbox(v_a_940_) as u8);
                lean_dec(v_a_940_);
                if v___x_944_ == 0 {
                    v___x_945_ = 1;
                    v___x_946_ = lean_box((v___x_945_) as usize);
                    if v_isShared_943_ == 0 {
                        lean_ctor_set(v___x_942_, 0, v___x_946_);
                        v___x_948_ = v___x_942_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
                        v___x_948_ = v_reuseFailAlloc_949_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_950_ = 0;
                    v___x_951_ = lean_box((v___x_950_) as usize);
                    if v_isShared_943_ == 0 {
                        lean_ctor_set(v___x_942_, 0, v___x_951_);
                        v___x_953_ = v___x_942_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
                        v___x_953_ = v_reuseFailAlloc_954_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_948_;
            }
            3 => {
                return v___x_953_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1___boxed(
    mut v_declName_956_: *mut LeanObject,
    mut v___y_957_: *mut LeanObject,
    mut v___y_958_: *mut LeanObject,
    mut v___y_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_960_: *mut LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1(v_declName_956_, v___y_957_, v___y_958_);
    lean_dec(v___y_958_);
    lean_dec_ref(v___y_957_);
    return v_res_960_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    v___x_962_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_;
    v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
    return v___x_963_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    v___x_965_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_;
    v___x_966_ = l_Lean_stringToMessageData(v___x_965_);
    return v___x_966_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_(
    mut v_declName_967_: *mut LeanObject,
    mut v_x_968_: *mut LeanObject,
    mut v_kind_969_: u8,
    mut v___y_970_: *mut LeanObject,
    mut v___y_971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: u8 = 0;
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: u8 = 0;
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_991_: u8 = 0;
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_967_);
                v___x_978_ = l_Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1(v_declName_967_, v___y_970_, v___y_971_);
                if lean_obj_tag(v___x_978_) == 0 {
                    v_a_979_ = lean_ctor_get(v___x_978_, 0);
                    lean_inc(v_a_979_);
                    lean_dec_ref_known(v___x_978_, 1);
                    v___x_980_ = (lean_unbox(v_a_979_) as u8);
                    lean_dec(v_a_979_);
                    if v___x_980_ == 0 {
                        v___y_974_ = v___y_970_;
                        v___y_975_ = v___y_971_;
                        state = 1;
                        continue;
                    } else {
                        v___x_981_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_);
                        v___x_982_ = 0;
                        v___x_983_ = l_Lean_MessageData_ofConstName(v_declName_967_, v___x_982_);
                        v___x_984_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_984_, 0, v___x_981_);
                        lean_ctor_set(v___x_984_, 1, v___x_983_);
                        v___x_985_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_);
                        v___x_986_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_986_, 0, v___x_984_);
                        lean_ctor_set(v___x_986_, 1, v___x_985_);
                        v___x_987_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2___redArg(v___x_986_, v___y_970_, v___y_971_);
                        return v___x_987_;
                    }
                } else {
                    lean_dec(v_declName_967_);
                    v_a_988_ = lean_ctor_get(v___x_978_, 0);
                    v_isSharedCheck_995_ = (!lean_is_exclusive(v___x_978_)) as u8;
                    if v_isSharedCheck_995_ == 0 {
                        v___x_990_ = v___x_978_;
                        v_isShared_991_ = v_isSharedCheck_995_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_988_);
                        lean_dec(v___x_978_);
                        v___x_990_ = lean_box(0);
                        v_isShared_991_ = v_isSharedCheck_995_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_976_ = l_Lean_Meta_Tactic_Cbv_cbvOpaqueExt;
                v___x_977_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg(v___x_976_, v_declName_967_, v_kind_969_, v___y_974_, v___y_975_);
                return v___x_977_;
            }
            2 => {
                if v_isShared_991_ == 0 {
                    v___x_993_ = v___x_990_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
                    v___x_993_ = v_reuseFailAlloc_994_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2____boxed(
    mut v_declName_996_: *mut LeanObject,
    mut v_x_997_: *mut LeanObject,
    mut v_kind_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
    mut v___y_1000_: *mut LeanObject,
    mut v___y_1001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_1002_: u8 = 0;
    let mut v_res_1003_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_1002_ = (lean_unbox(v_kind_998_) as u8);
    v_res_1003_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_(v_declName_996_, v_x_997_, v_kind_boxed_1002_, v___y_999_, v___y_1000_);
    lean_dec(v___y_1000_);
    lean_dec_ref(v___y_999_);
    lean_dec(v_x_997_);
    return v_res_1003_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3_spec__5___redArg(
    mut v_a_1004_: *mut LeanObject,
    mut v_x_1005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1011_: u8 = 0;
    let mut v___x_1012_: u8 = 0;
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1005_) == 0 {
                    return v_x_1005_;
                } else {
                    v_key_1006_ = lean_ctor_get(v_x_1005_, 0);
                    v_value_1007_ = lean_ctor_get(v_x_1005_, 1);
                    v_tail_1008_ = lean_ctor_get(v_x_1005_, 2);
                    v_isSharedCheck_1017_ = (!lean_is_exclusive(v_x_1005_)) as u8;
                    if v_isSharedCheck_1017_ == 0 {
                        v___x_1010_ = v_x_1005_;
                        v_isShared_1011_ = v_isSharedCheck_1017_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1008_);
                        lean_inc(v_value_1007_);
                        lean_inc(v_key_1006_);
                        lean_dec(v_x_1005_);
                        v___x_1010_ = lean_box(0);
                        v_isShared_1011_ = v_isSharedCheck_1017_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1012_ = lean_name_eq(v_key_1006_, v_a_1004_);
                if v___x_1012_ == 0 {
                    v___x_1013_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3_spec__5___redArg(v_a_1004_, v_tail_1008_);
                    if v_isShared_1011_ == 0 {
                        lean_ctor_set(v___x_1010_, 2, v___x_1013_);
                        v___x_1015_ = v___x_1010_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_key_1006_);
                        lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_value_1007_);
                        lean_ctor_set(v_reuseFailAlloc_1016_, 2, v___x_1013_);
                        v___x_1015_ = v_reuseFailAlloc_1016_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1010_);
                    lean_dec(v_value_1007_);
                    lean_dec(v_key_1006_);
                    return v_tail_1008_;
                }
            }
            2 => {
                return v___x_1015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3_spec__5___redArg___boxed(
    mut v_a_1018_: *mut LeanObject,
    mut v_x_1019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1020_: *mut LeanObject = core::ptr::null_mut();
    v_res_1020_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3_spec__5___redArg(v_a_1018_, v_x_1019_);
    lean_dec(v_a_1018_);
    return v_res_1020_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3___redArg(
    mut v_m_1021_: *mut LeanObject,
    mut v_a_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1027_: u64 = 0;
    let mut v___x_1028_: u64 = 0;
    let mut v___x_1029_: u64 = 0;
    let mut v_fold_1030_: u64 = 0;
    let mut v___x_1031_: u64 = 0;
    let mut v___x_1032_: u64 = 0;
    let mut v___x_1033_: u64 = 0;
    let mut v___x_1034_: usize = 0;
    let mut v___x_1035_: usize = 0;
    let mut v___x_1036_: usize = 0;
    let mut v___x_1037_: usize = 0;
    let mut v___x_1038_: usize = 0;
    let mut v_bkt_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: u8 = 0;
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1043_: u8 = 0;
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1053_: u8 = 0;
    let mut v_unused_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: u64 = 0;
    let mut v_hash_1057_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_1023_ = lean_ctor_get(v_m_1021_, 0);
                v_buckets_1024_ = lean_ctor_get(v_m_1021_, 1);
                v___x_1025_ = lean_array_get_size(v_buckets_1024_);
                if lean_obj_tag(v_a_1022_) == 0 {
                    v___x_1056_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_1027_ = v___x_1056_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1057_ = lean_ctor_get_uint64(
                        v_a_1022_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1027_ = v_hash_1057_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1028_ = 32u64;
                v___x_1029_ = lean_uint64_shift_right(v___y_1027_, v___x_1028_);
                v_fold_1030_ = lean_uint64_xor(v___y_1027_, v___x_1029_);
                v___x_1031_ = 16u64;
                v___x_1032_ = lean_uint64_shift_right(v_fold_1030_, v___x_1031_);
                v___x_1033_ = lean_uint64_xor(v_fold_1030_, v___x_1032_);
                v___x_1034_ = lean_uint64_to_usize(v___x_1033_);
                v___x_1035_ = lean_usize_of_nat(v___x_1025_);
                v___x_1036_ = 1usize;
                v___x_1037_ = lean_usize_sub(v___x_1035_, v___x_1036_);
                v___x_1038_ = lean_usize_land(v___x_1034_, v___x_1037_);
                v_bkt_1039_ = lean_array_uget_borrowed(v_buckets_1024_, v___x_1038_);
                v___x_1040_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_1022_, v_bkt_1039_);
                if v___x_1040_ == 0 {
                    return v_m_1021_;
                } else {
                    lean_inc(v_bkt_1039_);
                    lean_inc_ref(v_buckets_1024_);
                    lean_inc(v_size_1023_);
                    v_isSharedCheck_1053_ = (!lean_is_exclusive(v_m_1021_)) as u8;
                    if v_isSharedCheck_1053_ == 0 {
                        v_unused_1054_ = lean_ctor_get(v_m_1021_, 1);
                        lean_dec(v_unused_1054_);
                        v_unused_1055_ = lean_ctor_get(v_m_1021_, 0);
                        lean_dec(v_unused_1055_);
                        v___x_1042_ = v_m_1021_;
                        v_isShared_1043_ = v_isSharedCheck_1053_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_1021_);
                        v___x_1042_ = lean_box(0);
                        v_isShared_1043_ = v_isSharedCheck_1053_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1044_ = lean_box(0);
                v_buckets_x27_1045_ = lean_array_uset(v_buckets_1024_, v___x_1038_, v___x_1044_);
                v___x_1046_ = lean_unsigned_to_nat(1);
                v___x_1047_ = lean_nat_sub(v_size_1023_, v___x_1046_);
                lean_dec(v_size_1023_);
                v___x_1048_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3_spec__5___redArg(v_a_1022_, v_bkt_1039_);
                v___x_1049_ = lean_array_uset(v_buckets_x27_1045_, v___x_1038_, v___x_1048_);
                if v_isShared_1043_ == 0 {
                    lean_ctor_set(v___x_1042_, 1, v___x_1049_);
                    lean_ctor_set(v___x_1042_, 0, v___x_1047_);
                    v___x_1051_ = v___x_1042_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1047_);
                    lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1049_);
                    v___x_1051_ = v_reuseFailAlloc_1052_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1051_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3___redArg___boxed(
    mut v_m_1058_: *mut LeanObject,
    mut v_a_1059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1060_: *mut LeanObject = core::ptr::null_mut();
    v_res_1060_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3___redArg(v_m_1058_, v_a_1059_);
    lean_dec(v_a_1059_);
    return v_res_1060_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_(
    mut v___x_1061_: *mut LeanObject,
    mut v_declName_1062_: *mut LeanObject,
    mut v_x_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    v___x_1064_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3___redArg(v___x_1061_, v_declName_1062_);
    return v___x_1064_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2____boxed(
    mut v___x_1065_: *mut LeanObject,
    mut v_declName_1066_: *mut LeanObject,
    mut v_x_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1068_: *mut LeanObject = core::ptr::null_mut();
    v_res_1068_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_(v___x_1065_, v_declName_1066_, v_x_1067_);
    lean_dec_ref(v_x_1067_);
    lean_dec(v_declName_1066_);
    return v_res_1068_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_(
    mut v___x_1069_: *mut LeanObject,
    mut v_declName_1070_: *mut LeanObject,
    mut v___y_1071_: *mut LeanObject,
    mut v___y_1072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1091_: u8 = 0;
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1102_: u8 = 0;
    let mut v_unused_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1074_ = lean_st_ref_get(v___y_1072_);
                v___x_1075_ = lean_st_ref_take(v___y_1072_);
                v_env_1076_ = lean_ctor_get(v___x_1074_, 0);
                lean_inc_ref(v_env_1076_);
                lean_dec(v___x_1074_);
                v___x_1077_ = l_Lean_Meta_Tactic_Cbv_cbvOpaqueExt;
                v_ext_1078_ = lean_ctor_get(v___x_1077_, 1);
                v_toEnvExtension_1079_ = lean_ctor_get(v_ext_1078_, 0);
                v_asyncMode_1080_ = lean_ctor_get(v_toEnvExtension_1079_, 2);
                v_env_1081_ = lean_ctor_get(v___x_1075_, 0);
                v_nextMacroScope_1082_ = lean_ctor_get(v___x_1075_, 1);
                v_ngen_1083_ = lean_ctor_get(v___x_1075_, 2);
                v_auxDeclNGen_1084_ = lean_ctor_get(v___x_1075_, 3);
                v_traceState_1085_ = lean_ctor_get(v___x_1075_, 4);
                v_messages_1086_ = lean_ctor_get(v___x_1075_, 6);
                v_infoState_1087_ = lean_ctor_get(v___x_1075_, 7);
                v_snapshotTasks_1088_ = lean_ctor_get(v___x_1075_, 8);
                v_isSharedCheck_1102_ = (!lean_is_exclusive(v___x_1075_)) as u8;
                if v_isSharedCheck_1102_ == 0 {
                    v_unused_1103_ = lean_ctor_get(v___x_1075_, 5);
                    lean_dec(v_unused_1103_);
                    v___x_1090_ = v___x_1075_;
                    v_isShared_1091_ = v_isSharedCheck_1102_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1088_);
                    lean_inc(v_infoState_1087_);
                    lean_inc(v_messages_1086_);
                    lean_inc(v_traceState_1085_);
                    lean_inc(v_auxDeclNGen_1084_);
                    lean_inc(v_ngen_1083_);
                    lean_inc(v_nextMacroScope_1082_);
                    lean_inc(v_env_1081_);
                    lean_dec(v___x_1075_);
                    v___x_1090_ = lean_box(0);
                    v_isShared_1091_ = v_isSharedCheck_1102_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1092_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_1069_,
                    v___x_1077_,
                    v_env_1076_,
                    v_asyncMode_1080_,
                );
                v___f_1093_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_1093_, 0, v___x_1092_);
                lean_closure_set(v___f_1093_, 1, v_declName_1070_);
                v___x_1094_ = l_Lean_ScopedEnvExtension_modifyState___redArg(
                    v___x_1077_,
                    v_env_1081_,
                    v___f_1093_,
                );
                v___x_1095_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__0___redArg___closed__2);
                if v_isShared_1091_ == 0 {
                    lean_ctor_set(v___x_1090_, 5, v___x_1095_);
                    lean_ctor_set(v___x_1090_, 0, v___x_1094_);
                    v___x_1097_ = v___x_1090_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1094_);
                    lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_nextMacroScope_1082_);
                    lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_ngen_1083_);
                    lean_ctor_set(v_reuseFailAlloc_1101_, 3, v_auxDeclNGen_1084_);
                    lean_ctor_set(v_reuseFailAlloc_1101_, 4, v_traceState_1085_);
                    lean_ctor_set(v_reuseFailAlloc_1101_, 5, v___x_1095_);
                    lean_ctor_set(v_reuseFailAlloc_1101_, 6, v_messages_1086_);
                    lean_ctor_set(v_reuseFailAlloc_1101_, 7, v_infoState_1087_);
                    lean_ctor_set(v_reuseFailAlloc_1101_, 8, v_snapshotTasks_1088_);
                    v___x_1097_ = v_reuseFailAlloc_1101_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1098_ = lean_st_ref_set(v___y_1072_, v___x_1097_);
                v___x_1099_ = lean_box(0);
                v___x_1100_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1100_, 0, v___x_1099_);
                return v___x_1100_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2____boxed(
    mut v___x_1104_: *mut LeanObject,
    mut v_declName_1105_: *mut LeanObject,
    mut v___y_1106_: *mut LeanObject,
    mut v___y_1107_: *mut LeanObject,
    mut v___y_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1109_: *mut LeanObject = core::ptr::null_mut();
    v_res_1109_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_(v___x_1104_, v_declName_1105_, v___y_1106_, v___y_1107_);
    lean_dec(v___y_1107_);
    lean_dec_ref(v___y_1106_);
    lean_dec_ref(v___x_1104_);
    return v_res_1109_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    v___x_1113_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_;
    v___x_1114_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_;
    v___x_1115_ = l_Std_HashSet_instInhabited(lean_box(0), v___x_1114_, v___x_1113_);
    return v___x_1115_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1117_: *mut LeanObject = core::ptr::null_mut();
    v___x_1116_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_);
    v___f_1117_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 5, 1);
    lean_closure_set(v___f_1117_, 0, v___x_1116_);
    return v___f_1117_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    v___f_1130_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_);
    v___f_1131_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_;
    v___x_1132_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_;
    v___x_1133_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1133_, 0, v___x_1132_);
    lean_ctor_set(v___x_1133_, 1, v___f_1131_);
    lean_ctor_set(v___x_1133_, 2, v___f_1130_);
    return v___x_1133_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    v___x_1135_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_);
    v___x_1136_ = l_Lean_registerBuiltinAttribute(v___x_1135_);
    return v___x_1136_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2____boxed(
    mut v_a_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1138_: *mut LeanObject = core::ptr::null_mut();
    v_res_1138_ = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_();
    return v_res_1138_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1_spec__1(
    mut v_declName_1139_: *mut LeanObject,
    mut v___y_1140_: *mut LeanObject,
    mut v___y_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    v___x_1143_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1_spec__1___redArg(v_declName_1139_, v___y_1141_);
    return v___x_1143_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1_spec__1___boxed(
    mut v_declName_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1148_: *mut LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Lean_getReducibilityStatus___at___00Lean_isReducible___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__1_spec__1(v_declName_1144_, v___y_1145_, v___y_1146_);
    lean_dec(v___y_1146_);
    lean_dec_ref(v___y_1145_);
    return v_res_1148_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2(
    mut v_00_u03b1_1149_: *mut LeanObject,
    mut v_msg_1150_: *mut LeanObject,
    mut v___y_1151_: *mut LeanObject,
    mut v___y_1152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    v___x_1154_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2___redArg(v_msg_1150_, v___y_1151_, v___y_1152_);
    return v___x_1154_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2___boxed(
    mut v_00_u03b1_1155_: *mut LeanObject,
    mut v_msg_1156_: *mut LeanObject,
    mut v___y_1157_: *mut LeanObject,
    mut v___y_1158_: *mut LeanObject,
    mut v___y_1159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1160_: *mut LeanObject = core::ptr::null_mut();
    v_res_1160_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__2(v_00_u03b1_1155_, v_msg_1156_, v___y_1157_, v___y_1158_);
    lean_dec(v___y_1158_);
    lean_dec_ref(v___y_1157_);
    return v_res_1160_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3(
    mut v_00_u03b2_1161_: *mut LeanObject,
    mut v_m_1162_: *mut LeanObject,
    mut v_a_1163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3___redArg(v_m_1162_, v_a_1163_);
    return v___x_1164_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3___boxed(
    mut v_00_u03b2_1165_: *mut LeanObject,
    mut v_m_1166_: *mut LeanObject,
    mut v_a_1167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1168_: *mut LeanObject = core::ptr::null_mut();
    v_res_1168_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3(v_00_u03b2_1165_, v_m_1166_, v_a_1167_);
    lean_dec(v_a_1167_);
    return v_res_1168_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3_spec__5(
    mut v_00_u03b2_1169_: *mut LeanObject,
    mut v_a_1170_: *mut LeanObject,
    mut v_x_1171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3_spec__5___redArg(v_a_1170_, v_x_1171_);
    return v___x_1172_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3_spec__5___boxed(
    mut v_00_u03b2_1173_: *mut LeanObject,
    mut v_a_1174_: *mut LeanObject,
    mut v_x_1175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1176_: *mut LeanObject = core::ptr::null_mut();
    v_res_1176_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__spec__3_spec__5(v_00_u03b2_1173_, v_a_1174_, v_x_1175_);
    lean_dec(v_a_1174_);
    return v_res_1176_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_cbvOpaque___redArg(
    mut v_a_1177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    v___x_1179_ = lean_st_ref_get(v_a_1177_);
    v_env_1180_ = lean_ctor_get(v___x_1179_, 0);
    lean_inc_ref(v_env_1180_);
    lean_dec(v___x_1179_);
    v___x_1181_ = l_Lean_Meta_Tactic_Cbv_cbvOpaqueExt;
    v_ext_1182_ = lean_ctor_get(v___x_1181_, 1);
    v_toEnvExtension_1183_ = lean_ctor_get(v_ext_1182_, 0);
    v_asyncMode_1184_ = lean_ctor_get(v_toEnvExtension_1183_, 2);
    v___x_1185_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_);
    v___x_1186_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_1185_,
        v___x_1181_,
        v_env_1180_,
        v_asyncMode_1184_,
    );
    v___x_1187_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1187_, 0, v___x_1186_);
    return v___x_1187_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_cbvOpaque___redArg___boxed(
    mut v_a_1188_: *mut LeanObject,
    mut v_a_1189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1190_: *mut LeanObject = core::ptr::null_mut();
    v_res_1190_ = l_Lean_Meta_Tactic_Cbv_cbvOpaque___redArg(v_a_1188_);
    lean_dec(v_a_1188_);
    return v_res_1190_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_cbvOpaque(
    mut v_a_1191_: *mut LeanObject,
    mut v_a_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    v___x_1194_ = l_Lean_Meta_Tactic_Cbv_cbvOpaque___redArg(v_a_1192_);
    return v___x_1194_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_cbvOpaque___boxed(
    mut v_a_1195_: *mut LeanObject,
    mut v_a_1196_: *mut LeanObject,
    mut v_a_1197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1198_: *mut LeanObject = core::ptr::null_mut();
    v_res_1198_ = l_Lean_Meta_Tactic_Cbv_cbvOpaque(v_a_1195_, v_a_1196_);
    lean_dec(v_a_1196_);
    lean_dec_ref(v_a_1195_);
    return v_res_1198_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_isCbvOpaque_spec__0___redArg(
    mut v_m_1199_: *mut LeanObject,
    mut v_a_1200_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1204_: u64 = 0;
    let mut v___x_1205_: u64 = 0;
    let mut v___x_1206_: u64 = 0;
    let mut v_fold_1207_: u64 = 0;
    let mut v___x_1208_: u64 = 0;
    let mut v___x_1209_: u64 = 0;
    let mut v___x_1210_: u64 = 0;
    let mut v___x_1211_: usize = 0;
    let mut v___x_1212_: usize = 0;
    let mut v___x_1213_: usize = 0;
    let mut v___x_1214_: usize = 0;
    let mut v___x_1215_: usize = 0;
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: u64 = 0;
    let mut v_hash_1219_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1201_ = lean_ctor_get(v_m_1199_, 1);
                v___x_1202_ = lean_array_get_size(v_buckets_1201_);
                if lean_obj_tag(v_a_1200_) == 0 {
                    v___x_1218_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
                    v___y_1204_ = v___x_1218_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1219_ = lean_ctor_get_uint64(
                        v_a_1200_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    v___y_1204_ = v_hash_1219_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1205_ = 32u64;
                v___x_1206_ = lean_uint64_shift_right(v___y_1204_, v___x_1205_);
                v_fold_1207_ = lean_uint64_xor(v___y_1204_, v___x_1206_);
                v___x_1208_ = 16u64;
                v___x_1209_ = lean_uint64_shift_right(v_fold_1207_, v___x_1208_);
                v___x_1210_ = lean_uint64_xor(v_fold_1207_, v___x_1209_);
                v___x_1211_ = lean_uint64_to_usize(v___x_1210_);
                v___x_1212_ = lean_usize_of_nat(v___x_1202_);
                v___x_1213_ = 1usize;
                v___x_1214_ = lean_usize_sub(v___x_1212_, v___x_1213_);
                v___x_1215_ = lean_usize_land(v___x_1211_, v___x_1214_);
                v___x_1216_ = lean_array_uget_borrowed(v_buckets_1201_, v___x_1215_);
                v___x_1217_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_1200_, v___x_1216_);
                return v___x_1217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_isCbvOpaque_spec__0___redArg___boxed(
    mut v_m_1220_: *mut LeanObject,
    mut v_a_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1222_: u8 = 0;
    let mut v_r_1223_: *mut LeanObject = core::ptr::null_mut();
    v_res_1222_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_isCbvOpaque_spec__0___redArg(v_m_1220_, v_a_1221_);
    lean_dec(v_a_1221_);
    lean_dec_ref(v_m_1220_);
    v_r_1223_ = lean_box((v_res_1222_) as usize);
    return v_r_1223_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(
    mut v_name_1224_: *mut LeanObject,
    mut v_a_1225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: u8 = 0;
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    v___x_1227_ = lean_st_ref_get(v_a_1225_);
    v_env_1228_ = lean_ctor_get(v___x_1227_, 0);
    lean_inc_ref(v_env_1228_);
    lean_dec(v___x_1227_);
    v___x_1229_ = l_Lean_Meta_Tactic_Cbv_cbvOpaqueExt;
    v_ext_1230_ = lean_ctor_get(v___x_1229_, 1);
    v_toEnvExtension_1231_ = lean_ctor_get(v_ext_1230_, 0);
    v_asyncMode_1232_ = lean_ctor_get(v_toEnvExtension_1231_, 2);
    v___x_1233_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_);
    v___x_1234_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_1233_,
        v___x_1229_,
        v_env_1228_,
        v_asyncMode_1232_,
    );
    v___x_1235_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_isCbvOpaque_spec__0___redArg(v___x_1234_, v_name_1224_);
    lean_dec(v___x_1234_);
    v___x_1236_ = lean_box((v___x_1235_) as usize);
    v___x_1237_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1237_, 0, v___x_1236_);
    return v___x_1237_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg___boxed(
    mut v_name_1238_: *mut LeanObject,
    mut v_a_1239_: *mut LeanObject,
    mut v_a_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1241_: *mut LeanObject = core::ptr::null_mut();
    v_res_1241_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_name_1238_, v_a_1239_);
    lean_dec(v_a_1239_);
    lean_dec(v_name_1238_);
    return v_res_1241_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isCbvOpaque(
    mut v_name_1242_: *mut LeanObject,
    mut v_a_1243_: *mut LeanObject,
    mut v_a_1244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_name_1242_, v_a_1244_);
    return v___x_1246_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isCbvOpaque___boxed(
    mut v_name_1247_: *mut LeanObject,
    mut v_a_1248_: *mut LeanObject,
    mut v_a_1249_: *mut LeanObject,
    mut v_a_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1251_: *mut LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque(v_name_1247_, v_a_1248_, v_a_1249_);
    lean_dec(v_a_1249_);
    lean_dec_ref(v_a_1248_);
    lean_dec(v_name_1247_);
    return v_res_1251_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_isCbvOpaque_spec__0(
    mut v_00_u03b2_1252_: *mut LeanObject,
    mut v_m_1253_: *mut LeanObject,
    mut v_a_1254_: *mut LeanObject,
) -> u8 {
    let mut v___x_1255_: u8 = 0;
    v___x_1255_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_isCbvOpaque_spec__0___redArg(v_m_1253_, v_a_1254_);
    return v___x_1255_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_isCbvOpaque_spec__0___boxed(
    mut v_00_u03b2_1256_: *mut LeanObject,
    mut v_m_1257_: *mut LeanObject,
    mut v_a_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1259_: u8 = 0;
    let mut v_r_1260_: *mut LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_isCbvOpaque_spec__0(v_00_u03b2_1256_, v_m_1257_, v_a_1258_);
    lean_dec(v_a_1258_);
    lean_dec_ref(v_m_1257_);
    v_r_1260_ = lean_box((v_res_1259_) as usize);
    return v_r_1260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ReducibilityAttrs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_1973793274____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Tactic_Cbv_cbvOpaqueExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbvOpaqueExt);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_Opaque_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Opaque_2610012288____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ScopedEnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ReducibilityAttrs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
}
