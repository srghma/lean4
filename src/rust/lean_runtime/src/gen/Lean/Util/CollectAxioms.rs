// Lean compiler output
// Module: Lean.Util.CollectAxioms
// Imports: Lean.MonadEnv
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_instInhabitedForall___redArg___lam__0___boxed, l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_lt, l_Lean_Name_quickLt};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg, lean_environment_find,
};
use crate::r#gen::Lean::MonadEnv::{initialize_Lean_MonadEnv, runtime_initialize_Lean_MonadEnv};
use crate::r#gen::Lean::Util::FoldConsts::l_Lean_Expr_getUsedConstants;
use crate::lean_imports_rs::Init::Core::lean_task_get_own;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_apply_4, lean_box, lean_box_usize, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0_value:
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
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0_value
) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5_value) as *mut LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6_value) as *mut LeanObject;
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 46, 99, 111, 108, 108, 101, 99, 116, 65, 110, 100, 71, 101, 116, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 111, 108, 108, 101, 99, 116, 65, 110, 100, 71, 101, 116, 58, 32, 39, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [39, 32, 110, 111, 116, 32, 105, 110, 32, 115, 101, 101, 110, 32, 97, 102, 116, 101, 114, 32, 99, 111, 108, 108, 101, 99, 116, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + core::mem::size_of::<usize>()*1) as u16, other: 1, tag: 0 }, m_objs: [(0 as *mut LeanObject)] };
pub static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 116, 105, 108, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,11246366368068211756 as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,16007987903351044003 as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,4211746031378004846 as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,14374199986448060823 as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 120, 112, 111, 114, 116, 101, 100, 65, 120, 105, 111, 109, 115, 69, 120, 116, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,14140705196984542656 as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanCtorObject<8> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    v___x_988_ = l_Lean_NameSet_empty;
    v___x_989_ = lean_box(1);
    v___x_990_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_990_, 0, v___x_989_);
    lean_ctor_set(v___x_990_, 1, v___x_988_);
    return v___x_990_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
    mut v_env_991_: *mut LeanObject,
    mut v_x_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_995_: *mut LeanObject = core::ptr::null_mut();
    v___x_993_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0_once), _init_l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0);
    v___x_994_ = lean_apply_2(v_x_992_, v_env_991_, v___x_993_);
    v_fst_995_ = lean_ctor_get(v___x_994_, 0);
    lean_inc(v_fst_995_);
    lean_dec_ref(v___x_994_);
    return v_fst_995_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM(
    mut v_00_u03b1_996_: *mut LeanObject,
    mut v_env_997_: *mut LeanObject,
    mut v_x_998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    v___x_999_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
        v_env_997_, v_x_998_,
    );
    return v___x_999_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(
    mut v_as_1000_: *mut LeanObject,
    mut v_i_1001_: usize,
    mut v_stop_1002_: usize,
    mut v_b_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: usize = 0;
    let mut v___x_1008_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1004_ = lean_usize_dec_eq(v_i_1001_, v_stop_1002_);
                if v___x_1004_ == 0 {
                    v___x_1005_ = lean_array_uget_borrowed(v_as_1000_, v_i_1001_);
                    lean_inc(v___x_1005_);
                    v___x_1006_ = l_Lean_NameSet_insert(v_b_1003_, v___x_1005_);
                    v___x_1007_ = 1usize;
                    v___x_1008_ = lean_usize_add(v_i_1001_, v___x_1007_);
                    v_i_1001_ = v___x_1008_;
                    v_b_1003_ = v___x_1006_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1003_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0___boxed(
    mut v_as_1010_: *mut LeanObject,
    mut v_i_1011_: *mut LeanObject,
    mut v_stop_1012_: *mut LeanObject,
    mut v_b_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1014_: usize = 0;
    let mut v_stop_boxed_1015_: usize = 0;
    let mut v_res_1016_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1014_ = lean_unbox_usize(v_i_1011_);
    lean_dec(v_i_1011_);
    v_stop_boxed_1015_ = lean_unbox_usize(v_stop_1012_);
    lean_dec(v_stop_1012_);
    v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_as_1010_, v_i_boxed_1014_, v_stop_boxed_1015_, v_b_1013_);
    lean_dec_ref(v_as_1010_);
    return v_res_1016_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
    mut v_s_1017_: *mut LeanObject,
    mut v_axs_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: u8 = 0;
    v___x_1019_ = lean_unsigned_to_nat(0);
    v___x_1020_ = lean_array_get_size(v_axs_1018_);
    v___x_1021_ = lean_nat_dec_lt(v___x_1019_, v___x_1020_);
    if v___x_1021_ == 0 {
        return v_s_1017_;
    } else {
        let mut v___x_1022_: u8 = 0;
        v___x_1022_ = lean_nat_dec_le(v___x_1020_, v___x_1020_);
        if v___x_1022_ == 0 {
            if v___x_1021_ == 0 {
                return v_s_1017_;
            } else {
                let mut v___x_1023_: usize = 0;
                let mut v___x_1024_: usize = 0;
                let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
                v___x_1023_ = 0usize;
                v___x_1024_ = lean_usize_of_nat(v___x_1020_);
                v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_axs_1018_, v___x_1023_, v___x_1024_, v_s_1017_);
                return v___x_1025_;
            }
        } else {
            let mut v___x_1026_: usize = 0;
            let mut v___x_1027_: usize = 0;
            let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
            v___x_1026_ = 0usize;
            v___x_1027_ = lean_usize_of_nat(v___x_1020_);
            v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_axs_1018_, v___x_1026_, v___x_1027_, v_s_1017_);
            return v___x_1028_;
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray___boxed(
    mut v_s_1029_: *mut LeanObject,
    mut v_axs_1030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1031_: *mut LeanObject = core::ptr::null_mut();
    v_res_1031_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
        v_s_1029_,
        v_axs_1030_,
    );
    lean_dec_ref(v_axs_1030_);
    return v_res_1031_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(
    mut v_init_1032_: *mut LeanObject,
    mut v_x_1033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1033_) == 0 {
                    v_k_1034_ = lean_ctor_get(v_x_1033_, 1);
                    lean_inc(v_k_1034_);
                    v_l_1035_ = lean_ctor_get(v_x_1033_, 3);
                    lean_inc(v_l_1035_);
                    v_r_1036_ = lean_ctor_get(v_x_1033_, 4);
                    lean_inc(v_r_1036_);
                    lean_dec_ref_known(v_x_1033_, 5);
                    v___x_1037_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v_init_1032_, v_l_1035_);
                    v___x_1038_ = lean_array_push(v___x_1037_, v_k_1034_);
                    v_init_1032_ = v___x_1038_;
                    v_x_1033_ = v_r_1036_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1032_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(
    mut v_hi_1040_: *mut LeanObject,
    mut v_pivot_1041_: *mut LeanObject,
    mut v_as_1042_: *mut LeanObject,
    mut v_i_1043_: *mut LeanObject,
    mut v_k_1044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1045_: u8 = 0;
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: u8 = 0;
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1045_ = lean_nat_dec_lt(v_k_1044_, v_hi_1040_);
                if v___x_1045_ == 0 {
                    lean_dec(v_k_1044_);
                    v___x_1046_ = lean_array_fswap(v_as_1042_, v_i_1043_, v_hi_1040_);
                    v___x_1047_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1047_, 0, v_i_1043_);
                    lean_ctor_set(v___x_1047_, 1, v___x_1046_);
                    return v___x_1047_;
                } else {
                    v___x_1048_ = lean_array_fget_borrowed(v_as_1042_, v_k_1044_);
                    v___x_1049_ = l_Lean_Name_lt(v___x_1048_, v_pivot_1041_);
                    if v___x_1049_ == 0 {
                        v___x_1050_ = lean_unsigned_to_nat(1);
                        v___x_1051_ = lean_nat_add(v_k_1044_, v___x_1050_);
                        lean_dec(v_k_1044_);
                        v_k_1044_ = v___x_1051_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1053_ = lean_array_fswap(v_as_1042_, v_i_1043_, v_k_1044_);
                        v___x_1054_ = lean_unsigned_to_nat(1);
                        v___x_1055_ = lean_nat_add(v_i_1043_, v___x_1054_);
                        lean_dec(v_i_1043_);
                        v___x_1056_ = lean_nat_add(v_k_1044_, v___x_1054_);
                        lean_dec(v_k_1044_);
                        v_as_1042_ = v___x_1053_;
                        v_i_1043_ = v___x_1055_;
                        v_k_1044_ = v___x_1056_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg___boxed(
    mut v_hi_1058_: *mut LeanObject,
    mut v_pivot_1059_: *mut LeanObject,
    mut v_as_1060_: *mut LeanObject,
    mut v_i_1061_: *mut LeanObject,
    mut v_k_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1063_: *mut LeanObject = core::ptr::null_mut();
    v_res_1063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_1058_, v_pivot_1059_, v_as_1060_, v_i_1061_, v_k_1062_);
    lean_dec(v_pivot_1059_);
    lean_dec(v_hi_1058_);
    return v_res_1063_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(
    mut v_n_1064_: *mut LeanObject,
    mut v_as_1065_: *mut LeanObject,
    mut v_lo_1066_: *mut LeanObject,
    mut v_hi_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: u8 = 0;
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: u8 = 0;
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1079_ = lean_nat_dec_lt(v_lo_1066_, v_hi_1067_);
                if v___x_1079_ == 0 {
                    lean_dec(v_lo_1066_);
                    return v_as_1065_;
                } else {
                    v___x_1080_ = lean_nat_add(v_lo_1066_, v_hi_1067_);
                    v___x_1081_ = lean_unsigned_to_nat(1);
                    v_mid_1082_ = lean_nat_shiftr(v___x_1080_, v___x_1081_);
                    lean_dec(v___x_1080_);
                    v___x_1095_ = lean_array_fget_borrowed(v_as_1065_, v_mid_1082_);
                    v___x_1096_ = lean_array_fget_borrowed(v_as_1065_, v_lo_1066_);
                    v___x_1097_ = l_Lean_Name_lt(v___x_1095_, v___x_1096_);
                    if v___x_1097_ == 0 {
                        v___y_1090_ = v_as_1065_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1098_ = lean_array_fswap(v_as_1065_, v_lo_1066_, v_mid_1082_);
                        v___y_1090_ = v___x_1098_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1070_ = lean_array_fget(v___y_1069_, v_hi_1067_);
                lean_inc_n(v_lo_1066_, 2);
                v___x_1071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_1067_, v_pivot_1070_, v___y_1069_, v_lo_1066_, v_lo_1066_);
                lean_dec(v_pivot_1070_);
                v_fst_1072_ = lean_ctor_get(v___x_1071_, 0);
                lean_inc(v_fst_1072_);
                v_snd_1073_ = lean_ctor_get(v___x_1071_, 1);
                lean_inc(v_snd_1073_);
                lean_dec_ref(v___x_1071_);
                v___x_1074_ = lean_nat_dec_le(v_hi_1067_, v_fst_1072_);
                if v___x_1074_ == 0 {
                    v___x_1075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_1064_, v_snd_1073_, v_lo_1066_, v_fst_1072_);
                    v___x_1076_ = lean_unsigned_to_nat(1);
                    v___x_1077_ = lean_nat_add(v_fst_1072_, v___x_1076_);
                    lean_dec(v_fst_1072_);
                    v_as_1065_ = v___x_1075_;
                    v_lo_1066_ = v___x_1077_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_1072_);
                    lean_dec(v_lo_1066_);
                    return v_snd_1073_;
                }
            }
            2 => {
                v___x_1085_ = lean_array_fget_borrowed(v___y_1084_, v_mid_1082_);
                v___x_1086_ = lean_array_fget_borrowed(v___y_1084_, v_hi_1067_);
                v___x_1087_ = l_Lean_Name_lt(v___x_1085_, v___x_1086_);
                if v___x_1087_ == 0 {
                    lean_dec(v_mid_1082_);
                    v___y_1069_ = v___y_1084_;
                    state = 1;
                    continue;
                } else {
                    v___x_1088_ = lean_array_fswap(v___y_1084_, v_mid_1082_, v_hi_1067_);
                    lean_dec(v_mid_1082_);
                    v___y_1069_ = v___x_1088_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1091_ = lean_array_fget_borrowed(v___y_1090_, v_hi_1067_);
                v___x_1092_ = lean_array_fget_borrowed(v___y_1090_, v_lo_1066_);
                v___x_1093_ = l_Lean_Name_lt(v___x_1091_, v___x_1092_);
                if v___x_1093_ == 0 {
                    v___y_1084_ = v___y_1090_;
                    state = 2;
                    continue;
                } else {
                    v___x_1094_ = lean_array_fswap(v___y_1090_, v_lo_1066_, v_hi_1067_);
                    v___y_1084_ = v___x_1094_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg___boxed(
    mut v_n_1099_: *mut LeanObject,
    mut v_as_1100_: *mut LeanObject,
    mut v_lo_1101_: *mut LeanObject,
    mut v_hi_1102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1103_: *mut LeanObject = core::ptr::null_mut();
    v_res_1103_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_1099_, v_as_1100_, v_lo_1101_, v_hi_1102_);
    lean_dec(v_hi_1102_);
    lean_dec(v_n_1099_);
    return v_res_1103_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(
    mut v_extFind_x3f_1106_: *mut LeanObject,
    mut v_as_1107_: *mut LeanObject,
    mut v_i_1108_: usize,
    mut v_stop_1109_: usize,
    mut v_b_1110_: *mut LeanObject,
    mut v___y_1111_: *mut LeanObject,
    mut v___y_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1113_: u8 = 0;
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: usize = 0;
    let mut v___x_1119_: usize = 0;
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1113_ = lean_usize_dec_eq(v_i_1108_, v_stop_1109_);
                if v___x_1113_ == 0 {
                    v___x_1114_ = lean_array_uget_borrowed(v_as_1107_, v_i_1108_);
                    lean_inc(v___x_1114_);
                    lean_inc_ref(v_extFind_x3f_1106_);
                    v___x_1115_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
                        v_extFind_x3f_1106_,
                        v___x_1114_,
                        v___y_1111_,
                        v___y_1112_,
                    );
                    v_fst_1116_ = lean_ctor_get(v___x_1115_, 0);
                    lean_inc(v_fst_1116_);
                    v_snd_1117_ = lean_ctor_get(v___x_1115_, 1);
                    lean_inc(v_snd_1117_);
                    lean_dec_ref(v___x_1115_);
                    v___x_1118_ = 1usize;
                    v___x_1119_ = lean_usize_add(v_i_1108_, v___x_1118_);
                    v_i_1108_ = v___x_1119_;
                    v_b_1110_ = v_fst_1116_;
                    v___y_1112_ = v_snd_1117_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_extFind_x3f_1106_);
                    v___x_1121_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1121_, 0, v_b_1110_);
                    lean_ctor_set(v___x_1121_, 1, v___y_1112_);
                    return v___x_1121_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(
    mut v_extFind_x3f_1122_: *mut LeanObject,
    mut v_e_1123_: *mut LeanObject,
    mut v___y_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: u8 = 0;
    v___x_1126_ = l_Lean_Expr_getUsedConstants(v_e_1123_);
    v___x_1127_ = lean_unsigned_to_nat(0);
    v___x_1128_ = lean_array_get_size(v___x_1126_);
    v___x_1129_ = lean_box(0);
    v___x_1130_ = lean_nat_dec_lt(v___x_1127_, v___x_1128_);
    if v___x_1130_ == 0 {
        let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_1126_);
        lean_dec_ref(v_extFind_x3f_1122_);
        v___x_1131_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1131_, 0, v___x_1129_);
        lean_ctor_set(v___x_1131_, 1, v___y_1125_);
        return v___x_1131_;
    } else {
        let mut v___x_1132_: u8 = 0;
        v___x_1132_ = lean_nat_dec_le(v___x_1128_, v___x_1128_);
        if v___x_1132_ == 0 {
            if v___x_1130_ == 0 {
                let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___x_1126_);
                lean_dec_ref(v_extFind_x3f_1122_);
                v___x_1133_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1133_, 0, v___x_1129_);
                lean_ctor_set(v___x_1133_, 1, v___y_1125_);
                return v___x_1133_;
            } else {
                let mut v___x_1134_: usize = 0;
                let mut v___x_1135_: usize = 0;
                let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
                v___x_1134_ = 0usize;
                v___x_1135_ = lean_usize_of_nat(v___x_1128_);
                v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_1122_, v___x_1126_, v___x_1134_, v___x_1135_, v___x_1129_, v___y_1124_, v___y_1125_);
                lean_dec_ref(v___x_1126_);
                return v___x_1136_;
            }
        } else {
            let mut v___x_1137_: usize = 0;
            let mut v___x_1138_: usize = 0;
            let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
            v___x_1137_ = 0usize;
            v___x_1138_ = lean_usize_of_nat(v___x_1128_);
            v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_1122_, v___x_1126_, v___x_1137_, v___x_1138_, v___x_1129_, v___y_1124_, v___y_1125_);
            lean_dec_ref(v___x_1126_);
            return v___x_1139_;
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
    mut v_extFind_x3f_1140_: *mut LeanObject,
    mut v_c_1141_: *mut LeanObject,
    mut v_a_1142_: *mut LeanObject,
    mut v_a_1143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seen_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_axioms_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1158_: u8 = 0;
    let mut v_seen_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_axioms_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___y_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_seen_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1170_: u8 = 0;
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v_unused_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: u8 = 0;
    let mut v___y_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___y_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_axioms_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_axioms_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_extFind_x3f_1140_);
                lean_inc(v_c_1141_);
                lean_inc_ref(v_a_1142_);
                v___x_1144_ = lean_apply_2(v_extFind_x3f_1140_, v_a_1142_, v_c_1141_);
                if lean_obj_tag(v___x_1144_) == 1 {
                    lean_dec_ref(v_extFind_x3f_1140_);
                    v_val_1145_ = lean_ctor_get(v___x_1144_, 0);
                    lean_inc(v_val_1145_);
                    lean_dec_ref_known(v___x_1144_, 1);
                    v_seen_1146_ = lean_ctor_get(v_a_1143_, 0);
                    v_axioms_1147_ = lean_ctor_get(v_a_1143_, 1);
                    v_isSharedCheck_1158_ = (!lean_is_exclusive(v_a_1143_)) as u8;
                    if v_isSharedCheck_1158_ == 0 {
                        v___x_1149_ = v_a_1143_;
                        v_isShared_1150_ = v_isSharedCheck_1158_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_axioms_1147_);
                        lean_inc(v_seen_1146_);
                        lean_dec(v_a_1143_);
                        v___x_1149_ = lean_box(0);
                        v_isShared_1150_ = v_isSharedCheck_1158_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1144_);
                    v_seen_1159_ = lean_ctor_get(v_a_1143_, 0);
                    v_axioms_1160_ = lean_ctor_get(v_a_1143_, 1);
                    v_isSharedCheck_1265_ = (!lean_is_exclusive(v_a_1143_)) as u8;
                    if v_isSharedCheck_1265_ == 0 {
                        v___x_1162_ = v_a_1143_;
                        v_isShared_1163_ = v_isSharedCheck_1265_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_axioms_1160_);
                        lean_inc(v_seen_1159_);
                        lean_dec(v_a_1143_);
                        v___x_1162_ = lean_box(0);
                        v_isShared_1163_ = v_isSharedCheck_1265_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_val_1145_);
                v___x_1151_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_1141_, v_val_1145_, v_seen_1146_);
                v___x_1152_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
                    v_axioms_1147_,
                    v_val_1145_,
                );
                lean_dec(v_val_1145_);
                if v_isShared_1150_ == 0 {
                    lean_ctor_set(v___x_1149_, 1, v___x_1152_);
                    lean_ctor_set(v___x_1149_, 0, v___x_1151_);
                    v___x_1154_ = v___x_1149_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1151_);
                    lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1152_);
                    v___x_1154_ = v_reuseFailAlloc_1157_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1155_ = lean_box(0);
                v___x_1156_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1156_, 0, v___x_1155_);
                lean_ctor_set(v___x_1156_, 1, v___x_1154_);
                return v___x_1156_;
            }
            3 => {
                v___x_1214_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_seen_1159_, v_c_1141_);
                if lean_obj_tag(v___x_1214_) == 1 {
                    lean_dec(v_c_1141_);
                    lean_dec_ref(v_extFind_x3f_1140_);
                    v_val_1215_ = lean_ctor_get(v___x_1214_, 0);
                    lean_inc(v_val_1215_);
                    lean_dec_ref_known(v___x_1214_, 1);
                    v___x_1216_ =
                        l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
                            v_axioms_1160_,
                            v_val_1215_,
                        );
                    lean_dec(v_val_1215_);
                    if v_isShared_1163_ == 0 {
                        lean_ctor_set(v___x_1162_, 1, v___x_1216_);
                        v___x_1218_ = v___x_1162_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_seen_1159_);
                        lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1216_);
                        v___x_1218_ = v_reuseFailAlloc_1221_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1214_);
                    v_checked_1222_ = lean_ctor_get(v_a_1142_, 2);
                    v___x_1223_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0;
                    lean_inc(v_c_1141_);
                    v___x_1224_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_1141_, v___x_1223_, v_seen_1159_);
                    v___x_1225_ = l_Lean_NameSet_empty;
                    lean_inc(v___x_1224_);
                    if v_isShared_1163_ == 0 {
                        lean_ctor_set(v___x_1162_, 1, v___x_1225_);
                        lean_ctor_set(v___x_1162_, 0, v___x_1224_);
                        v___x_1227_ = v___x_1162_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1224_);
                        lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1225_);
                        v___x_1227_ = v_reuseFailAlloc_1264_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_seen_1167_ = lean_ctor_get(v___y_1165_, 0);
                v_isSharedCheck_1178_ = (!lean_is_exclusive(v___y_1165_)) as u8;
                if v_isSharedCheck_1178_ == 0 {
                    v_unused_1179_ = lean_ctor_get(v___y_1165_, 1);
                    lean_dec(v_unused_1179_);
                    v___x_1169_ = v___y_1165_;
                    v_isShared_1170_ = v_isSharedCheck_1178_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_seen_1167_);
                    lean_dec(v___y_1165_);
                    v___x_1169_ = lean_box(0);
                    v_isShared_1170_ = v_isSharedCheck_1178_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1171_ = lean_box(0);
                lean_inc_ref(v___y_1166_);
                v___x_1172_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_1141_, v___y_1166_, v_seen_1167_);
                v___x_1173_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
                    v_axioms_1160_,
                    v___y_1166_,
                );
                lean_dec_ref(v___y_1166_);
                if v_isShared_1170_ == 0 {
                    lean_ctor_set(v___x_1169_, 1, v___x_1173_);
                    lean_ctor_set(v___x_1169_, 0, v___x_1172_);
                    v___x_1175_ = v___x_1169_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1172_);
                    lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1173_);
                    v___x_1175_ = v_reuseFailAlloc_1177_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1176_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1176_, 0, v___x_1171_);
                lean_ctor_set(v___x_1176_, 1, v___x_1175_);
                return v___x_1176_;
            }
            7 => {
                v___x_1186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v___y_1181_, v___y_1183_, v___y_1182_, v___y_1185_);
                lean_dec(v___y_1185_);
                lean_dec(v___y_1181_);
                v___y_1165_ = v___y_1184_;
                v___y_1166_ = v___x_1186_;
                state = 4;
                continue;
            }
            8 => {
                v___x_1193_ = lean_nat_dec_le(v___y_1192_, v___y_1189_);
                if v___x_1193_ == 0 {
                    lean_dec(v___y_1189_);
                    lean_inc(v___y_1192_);
                    v___y_1181_ = v___y_1188_;
                    v___y_1182_ = v___y_1192_;
                    v___y_1183_ = v___y_1190_;
                    v___y_1184_ = v___y_1191_;
                    v___y_1185_ = v___y_1192_;
                    state = 7;
                    continue;
                } else {
                    v___y_1181_ = v___y_1188_;
                    v___y_1182_ = v___y_1192_;
                    v___y_1183_ = v___y_1190_;
                    v___y_1184_ = v___y_1191_;
                    v___y_1185_ = v___y_1189_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                v___x_1198_ = lean_mk_empty_array_with_capacity(v___y_1197_);
                lean_dec(v___y_1197_);
                v___x_1199_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v___x_1198_, v___y_1195_);
                v___x_1200_ = lean_array_get_size(v___x_1199_);
                v___x_1201_ = lean_unsigned_to_nat(0);
                v___x_1202_ = lean_nat_dec_eq(v___x_1200_, v___x_1201_);
                if v___x_1202_ == 0 {
                    v___x_1203_ = lean_unsigned_to_nat(1);
                    v___x_1204_ = lean_nat_sub(v___x_1200_, v___x_1203_);
                    v___x_1205_ = lean_nat_dec_le(v___x_1201_, v___x_1204_);
                    if v___x_1205_ == 0 {
                        lean_inc(v___x_1204_);
                        v___y_1188_ = v___x_1200_;
                        v___y_1189_ = v___x_1204_;
                        v___y_1190_ = v___x_1199_;
                        v___y_1191_ = v___y_1196_;
                        v___y_1192_ = v___x_1204_;
                        state = 8;
                        continue;
                    } else {
                        v___y_1188_ = v___x_1200_;
                        v___y_1189_ = v___x_1204_;
                        v___y_1190_ = v___x_1199_;
                        v___y_1191_ = v___y_1196_;
                        v___y_1192_ = v___x_1201_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___y_1165_ = v___y_1196_;
                    v___y_1166_ = v___x_1199_;
                    state = 4;
                    continue;
                }
            }
            10 => {
                if lean_obj_tag(v_axioms_1208_) == 0 {
                    v_size_1209_ = lean_ctor_get(v_axioms_1208_, 0);
                    lean_inc(v_size_1209_);
                    v___y_1195_ = v_axioms_1208_;
                    v___y_1196_ = v___y_1207_;
                    v___y_1197_ = v_size_1209_;
                    state = 9;
                    continue;
                } else {
                    v___x_1210_ = lean_unsigned_to_nat(0);
                    v___y_1195_ = v_axioms_1208_;
                    v___y_1196_ = v___y_1207_;
                    v___y_1197_ = v___x_1210_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_axioms_1213_ = lean_ctor_get(v___y_1212_, 1);
                lean_inc(v_axioms_1213_);
                v___y_1207_ = v___y_1212_;
                v_axioms_1208_ = v_axioms_1213_;
                state = 10;
                continue;
            }
            12 => {
                v___x_1219_ = lean_box(0);
                v___x_1220_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1220_, 0, v___x_1219_);
                lean_ctor_set(v___x_1220_, 1, v___x_1218_);
                return v___x_1220_;
            }
            13 => {
                lean_inc_ref(v_checked_1222_);
                v___x_1228_ = lean_task_get_own(v_checked_1222_);
                lean_inc(v_c_1141_);
                v___x_1229_ = lean_environment_find(v___x_1228_, v_c_1141_);
                if lean_obj_tag(v___x_1229_) == 0 {
                    lean_dec(v___x_1224_);
                    lean_dec_ref(v_extFind_x3f_1140_);
                    v___y_1207_ = v___x_1227_;
                    v_axioms_1208_ = v___x_1225_;
                    state = 10;
                    continue;
                } else {
                    v_val_1230_ = lean_ctor_get(v___x_1229_, 0);
                    lean_inc(v_val_1230_);
                    lean_dec_ref_known(v___x_1229_, 1);
                    match lean_obj_tag(v_val_1230_) {
                        0 => {
                            lean_dec_ref(v___x_1227_);
                            v_val_1231_ = lean_ctor_get(v_val_1230_, 0);
                            lean_inc_ref(v_val_1231_);
                            lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1232_ = lean_ctor_get(v_val_1231_, 0);
                            lean_inc_ref(v_toConstantVal_1232_);
                            lean_dec_ref(v_val_1231_);
                            v_type_1233_ = lean_ctor_get(v_toConstantVal_1232_, 2);
                            lean_inc_ref(v_type_1233_);
                            lean_dec_ref(v_toConstantVal_1232_);
                            lean_inc(v_c_1141_);
                            v___x_1234_ = l_Lean_NameSet_insert(v___x_1225_, v_c_1141_);
                            v___x_1235_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1235_, 0, v___x_1224_);
                            lean_ctor_set(v___x_1235_, 1, v___x_1234_);
                            v___x_1236_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1233_, v_a_1142_, v___x_1235_);
                            v_snd_1237_ = lean_ctor_get(v___x_1236_, 1);
                            lean_inc(v_snd_1237_);
                            lean_dec_ref(v___x_1236_);
                            v___y_1212_ = v_snd_1237_;
                            state = 11;
                            continue;
                        }
                        4 => {
                            lean_dec_ref_known(v_val_1230_, 1);
                            lean_dec(v___x_1224_);
                            lean_dec_ref(v_extFind_x3f_1140_);
                            v___y_1207_ = v___x_1227_;
                            v_axioms_1208_ = v___x_1225_;
                            state = 10;
                            continue;
                        }
                        5 => {
                            lean_dec(v___x_1224_);
                            v_val_1238_ = lean_ctor_get(v_val_1230_, 0);
                            lean_inc_ref(v_val_1238_);
                            lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1239_ = lean_ctor_get(v_val_1238_, 0);
                            lean_inc_ref(v_toConstantVal_1239_);
                            v_ctors_1240_ = lean_ctor_get(v_val_1238_, 4);
                            lean_inc(v_ctors_1240_);
                            lean_dec_ref(v_val_1238_);
                            v_type_1241_ = lean_ctor_get(v_toConstantVal_1239_, 2);
                            lean_inc_ref(v_type_1241_);
                            lean_dec_ref(v_toConstantVal_1239_);
                            lean_inc_ref(v_extFind_x3f_1140_);
                            v___x_1242_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1241_, v_a_1142_, v___x_1227_);
                            v_snd_1243_ = lean_ctor_get(v___x_1242_, 1);
                            lean_inc(v_snd_1243_);
                            lean_dec_ref(v___x_1242_);
                            v___x_1244_ = l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(v_extFind_x3f_1140_, v_ctors_1240_, v_a_1142_, v_snd_1243_);
                            v_snd_1245_ = lean_ctor_get(v___x_1244_, 1);
                            lean_inc(v_snd_1245_);
                            lean_dec_ref(v___x_1244_);
                            v___y_1212_ = v_snd_1245_;
                            state = 11;
                            continue;
                        }
                        6 => {
                            lean_dec(v___x_1224_);
                            v_val_1246_ = lean_ctor_get(v_val_1230_, 0);
                            lean_inc_ref(v_val_1246_);
                            lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1247_ = lean_ctor_get(v_val_1246_, 0);
                            lean_inc_ref(v_toConstantVal_1247_);
                            lean_dec_ref(v_val_1246_);
                            v_type_1248_ = lean_ctor_get(v_toConstantVal_1247_, 2);
                            lean_inc_ref(v_type_1248_);
                            lean_dec_ref(v_toConstantVal_1247_);
                            v___x_1249_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1248_, v_a_1142_, v___x_1227_);
                            v_snd_1250_ = lean_ctor_get(v___x_1249_, 1);
                            lean_inc(v_snd_1250_);
                            lean_dec_ref(v___x_1249_);
                            v___y_1212_ = v_snd_1250_;
                            state = 11;
                            continue;
                        }
                        7 => {
                            lean_dec(v___x_1224_);
                            v_val_1251_ = lean_ctor_get(v_val_1230_, 0);
                            lean_inc_ref(v_val_1251_);
                            lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1252_ = lean_ctor_get(v_val_1251_, 0);
                            lean_inc_ref(v_toConstantVal_1252_);
                            lean_dec_ref(v_val_1251_);
                            v_type_1253_ = lean_ctor_get(v_toConstantVal_1252_, 2);
                            lean_inc_ref(v_type_1253_);
                            lean_dec_ref(v_toConstantVal_1252_);
                            v___x_1254_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1253_, v_a_1142_, v___x_1227_);
                            v_snd_1255_ = lean_ctor_get(v___x_1254_, 1);
                            lean_inc(v_snd_1255_);
                            lean_dec_ref(v___x_1254_);
                            v___y_1212_ = v_snd_1255_;
                            state = 11;
                            continue;
                        }
                        _ => {
                            lean_dec(v___x_1224_);
                            v_val_1256_ = lean_ctor_get(v_val_1230_, 0);
                            lean_inc_ref(v_val_1256_);
                            lean_dec(v_val_1230_);
                            v_toConstantVal_1257_ = lean_ctor_get(v_val_1256_, 0);
                            lean_inc_ref(v_toConstantVal_1257_);
                            v_value_1258_ = lean_ctor_get(v_val_1256_, 1);
                            lean_inc_ref(v_value_1258_);
                            lean_dec_ref(v_val_1256_);
                            v_type_1259_ = lean_ctor_get(v_toConstantVal_1257_, 2);
                            lean_inc_ref(v_type_1259_);
                            lean_dec_ref(v_toConstantVal_1257_);
                            lean_inc_ref(v_extFind_x3f_1140_);
                            v___x_1260_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1259_, v_a_1142_, v___x_1227_);
                            v_snd_1261_ = lean_ctor_get(v___x_1260_, 1);
                            lean_inc(v_snd_1261_);
                            lean_dec_ref(v___x_1260_);
                            v___x_1262_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_value_1258_, v_a_1142_, v_snd_1261_);
                            v_snd_1263_ = lean_ctor_get(v___x_1262_, 1);
                            lean_inc(v_snd_1263_);
                            lean_dec_ref(v___x_1262_);
                            v___y_1212_ = v_snd_1263_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(
    mut v_extFind_x3f_1266_: *mut LeanObject,
    mut v_as_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
    mut v___y_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_1267_) == 0 {
                    lean_dec_ref(v_extFind_x3f_1266_);
                    v___x_1270_ = lean_box(0);
                    v___x_1271_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1271_, 0, v___x_1270_);
                    lean_ctor_set(v___x_1271_, 1, v___y_1269_);
                    return v___x_1271_;
                } else {
                    v_head_1272_ = lean_ctor_get(v_as_1267_, 0);
                    lean_inc(v_head_1272_);
                    v_tail_1273_ = lean_ctor_get(v_as_1267_, 1);
                    lean_inc(v_tail_1273_);
                    lean_dec_ref_known(v_as_1267_, 2);
                    lean_inc_ref(v_extFind_x3f_1266_);
                    v___x_1274_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
                        v_extFind_x3f_1266_,
                        v_head_1272_,
                        v___y_1268_,
                        v___y_1269_,
                    );
                    v_snd_1275_ = lean_ctor_get(v___x_1274_, 1);
                    lean_inc(v_snd_1275_);
                    lean_dec_ref(v___x_1274_);
                    v_as_1267_ = v_tail_1273_;
                    v___y_1269_ = v_snd_1275_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3___boxed(
    mut v_extFind_x3f_1277_: *mut LeanObject,
    mut v_as_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
    mut v___y_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1281_: *mut LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(v_extFind_x3f_1277_, v_as_1278_, v___y_1279_, v___y_1280_);
    lean_dec_ref(v___y_1279_);
    return v_res_1281_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0___boxed(
    mut v_extFind_x3f_1282_: *mut LeanObject,
    mut v_as_1283_: *mut LeanObject,
    mut v_i_1284_: *mut LeanObject,
    mut v_stop_1285_: *mut LeanObject,
    mut v_b_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
    mut v___y_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1289_: usize = 0;
    let mut v_stop_boxed_1290_: usize = 0;
    let mut v_res_1291_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1289_ = lean_unbox_usize(v_i_1284_);
    lean_dec(v_i_1284_);
    v_stop_boxed_1290_ = lean_unbox_usize(v_stop_1285_);
    lean_dec(v_stop_1285_);
    v_res_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_1282_, v_as_1283_, v_i_boxed_1289_, v_stop_boxed_1290_, v_b_1286_, v___y_1287_, v___y_1288_);
    lean_dec_ref(v___y_1287_);
    lean_dec_ref(v_as_1283_);
    return v_res_1291_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0___boxed(
    mut v_extFind_x3f_1292_: *mut LeanObject,
    mut v_e_1293_: *mut LeanObject,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1296_: *mut LeanObject = core::ptr::null_mut();
    v_res_1296_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(
        v_extFind_x3f_1292_,
        v_e_1293_,
        v___y_1294_,
        v___y_1295_,
    );
    lean_dec_ref(v___y_1294_);
    return v_res_1296_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___boxed(
    mut v_extFind_x3f_1297_: *mut LeanObject,
    mut v_c_1298_: *mut LeanObject,
    mut v_a_1299_: *mut LeanObject,
    mut v_a_1300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1301_: *mut LeanObject = core::ptr::null_mut();
    v_res_1301_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
        v_extFind_x3f_1297_,
        v_c_1298_,
        v_a_1299_,
        v_a_1300_,
    );
    lean_dec_ref(v_a_1299_);
    return v_res_1301_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1(
    mut v_init_1302_: *mut LeanObject,
    mut v_t_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    v___x_1304_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v_init_1302_, v_t_1303_);
    return v___x_1304_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(
    mut v_n_1305_: *mut LeanObject,
    mut v_as_1306_: *mut LeanObject,
    mut v_lo_1307_: *mut LeanObject,
    mut v_hi_1308_: *mut LeanObject,
    mut v_w_1309_: *mut LeanObject,
    mut v_hlo_1310_: *mut LeanObject,
    mut v_hhi_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    v___x_1312_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_1305_, v_as_1306_, v_lo_1307_, v_hi_1308_);
    return v___x_1312_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___boxed(
    mut v_n_1313_: *mut LeanObject,
    mut v_as_1314_: *mut LeanObject,
    mut v_lo_1315_: *mut LeanObject,
    mut v_hi_1316_: *mut LeanObject,
    mut v_w_1317_: *mut LeanObject,
    mut v_hlo_1318_: *mut LeanObject,
    mut v_hhi_1319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1320_: *mut LeanObject = core::ptr::null_mut();
    v_res_1320_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(v_n_1313_, v_as_1314_, v_lo_1315_, v_hi_1316_, v_w_1317_, v_hlo_1318_, v_hhi_1319_);
    lean_dec(v_hi_1316_);
    lean_dec(v_n_1313_);
    return v_res_1320_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(
    mut v_n_1321_: *mut LeanObject,
    mut v_lo_1322_: *mut LeanObject,
    mut v_hi_1323_: *mut LeanObject,
    mut v_hhi_1324_: *mut LeanObject,
    mut v_pivot_1325_: *mut LeanObject,
    mut v_as_1326_: *mut LeanObject,
    mut v_i_1327_: *mut LeanObject,
    mut v_k_1328_: *mut LeanObject,
    mut v_ilo_1329_: *mut LeanObject,
    mut v_ik_1330_: *mut LeanObject,
    mut v_w_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    v___x_1332_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_1323_, v_pivot_1325_, v_as_1326_, v_i_1327_, v_k_1328_);
    return v___x_1332_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___boxed(
    mut v_n_1333_: *mut LeanObject,
    mut v_lo_1334_: *mut LeanObject,
    mut v_hi_1335_: *mut LeanObject,
    mut v_hhi_1336_: *mut LeanObject,
    mut v_pivot_1337_: *mut LeanObject,
    mut v_as_1338_: *mut LeanObject,
    mut v_i_1339_: *mut LeanObject,
    mut v_k_1340_: *mut LeanObject,
    mut v_ilo_1341_: *mut LeanObject,
    mut v_ik_1342_: *mut LeanObject,
    mut v_w_1343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1344_: *mut LeanObject = core::ptr::null_mut();
    v_res_1344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(v_n_1333_, v_lo_1334_, v_hi_1335_, v_hhi_1336_, v_pivot_1337_, v_as_1338_, v_i_1339_, v_k_1340_, v_ilo_1341_, v_ik_1342_, v_w_1343_);
    lean_dec(v_pivot_1337_);
    lean_dec(v_hi_1335_);
    lean_dec(v_lo_1334_);
    lean_dec(v_n_1333_);
    return v_res_1344_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7()
-> *mut LeanObject {
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    v___x_1352_ = l_Array_instInhabited(lean_box(0));
    return v___x_1352_;
}
pub unsafe fn l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(
    mut v_msg_1353_: *mut LeanObject,
    mut v___y_1354_: *mut LeanObject,
    mut v___y_1355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017__overap_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    v___f_1356_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0;
    v___f_1357_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1;
    v___f_1358_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2;
    v___f_1359_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3;
    v___f_1360_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4;
    v___f_1361_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5;
    v___f_1362_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6;
    v___x_1363_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1363_, 0, v___f_1356_);
    lean_ctor_set(v___x_1363_, 1, v___f_1357_);
    v___x_1364_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1364_, 0, v___x_1363_);
    lean_ctor_set(v___x_1364_, 1, v___f_1358_);
    lean_ctor_set(v___x_1364_, 2, v___f_1359_);
    lean_ctor_set(v___x_1364_, 3, v___f_1360_);
    lean_ctor_set(v___x_1364_, 4, v___f_1361_);
    v___x_1365_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1365_, 0, v___x_1364_);
    lean_ctor_set(v___x_1365_, 1, v___f_1362_);
    lean_inc_ref_n(v___x_1365_, 6);
    v___f_1366_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1366_, 0, v___x_1365_);
    v___f_1367_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1367_, 0, v___x_1365_);
    v___f_1368_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1368_, 0, v___x_1365_);
    v___f_1369_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_1369_, 0, v___x_1365_);
    v___x_1370_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1370_, 0, lean_box(0));
    lean_closure_set(v___x_1370_, 1, lean_box(0));
    lean_closure_set(v___x_1370_, 2, v___x_1365_);
    v___x_1371_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1371_, 0, v___x_1370_);
    lean_ctor_set(v___x_1371_, 1, v___f_1366_);
    v___x_1372_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_1372_, 0, lean_box(0));
    lean_closure_set(v___x_1372_, 1, lean_box(0));
    lean_closure_set(v___x_1372_, 2, v___x_1365_);
    v___x_1373_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_1373_, 0, v___x_1371_);
    lean_ctor_set(v___x_1373_, 1, v___x_1372_);
    lean_ctor_set(v___x_1373_, 2, v___f_1367_);
    lean_ctor_set(v___x_1373_, 3, v___f_1368_);
    lean_ctor_set(v___x_1373_, 4, v___f_1369_);
    v___x_1374_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_1374_, 0, lean_box(0));
    lean_closure_set(v___x_1374_, 1, lean_box(0));
    lean_closure_set(v___x_1374_, 2, v___x_1365_);
    v___x_1375_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1375_, 0, v___x_1373_);
    lean_ctor_set(v___x_1375_, 1, v___x_1374_);
    v___x_1376_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7_once), _init_l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7);
    v___x_1377_ = l_instInhabitedOfMonad___redArg(v___x_1375_, v___x_1376_);
    v___f_1378_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1378_, 0, v___x_1377_);
    v___x_1017__overap_1379_ = lean_panic_fn_borrowed(v___f_1378_, v_msg_1353_);
    lean_dec_ref(v___f_1378_);
    lean_inc_ref(v___y_1354_);
    v___x_1380_ = lean_apply_2(v___x_1017__overap_1379_, v___y_1354_, v___y_1355_);
    return v___x_1380_;
}
pub unsafe fn l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___boxed(
    mut v_msg_1381_: *mut LeanObject,
    mut v___y_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1384_: *mut LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(v_msg_1381_, v___y_1382_, v___y_1383_);
    lean_dec_ref(v___y_1382_);
    return v_res_1384_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(
    mut v_extFind_x3f_1389_: *mut LeanObject,
    mut v_c_1390_: *mut LeanObject,
    mut v_a_1391_: *mut LeanObject,
    mut v_a_1392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1397_: u8 = 0;
    let mut v_seen_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: u8 = 0;
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1416_: u8 = 0;
    let mut v_unused_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_c_1390_);
                v___x_1393_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
                    v_extFind_x3f_1389_,
                    v_c_1390_,
                    v_a_1391_,
                    v_a_1392_,
                );
                v_snd_1394_ = lean_ctor_get(v___x_1393_, 1);
                v_isSharedCheck_1416_ = (!lean_is_exclusive(v___x_1393_)) as u8;
                if v_isSharedCheck_1416_ == 0 {
                    v_unused_1417_ = lean_ctor_get(v___x_1393_, 0);
                    lean_dec(v_unused_1417_);
                    v___x_1396_ = v___x_1393_;
                    v_isShared_1397_ = v_isSharedCheck_1416_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1394_);
                    lean_dec(v___x_1393_);
                    v___x_1396_ = lean_box(0);
                    v_isShared_1397_ = v_isSharedCheck_1416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_seen_1398_ = lean_ctor_get(v_snd_1394_, 0);
                v___x_1399_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_seen_1398_, v_c_1390_);
                if lean_obj_tag(v___x_1399_) == 1 {
                    lean_dec(v_c_1390_);
                    v_val_1400_ = lean_ctor_get(v___x_1399_, 0);
                    lean_inc(v_val_1400_);
                    lean_dec_ref_known(v___x_1399_, 1);
                    if v_isShared_1397_ == 0 {
                        lean_ctor_set(v___x_1396_, 0, v_val_1400_);
                        v___x_1402_ = v___x_1396_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_val_1400_);
                        lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_snd_1394_);
                        v___x_1402_ = v_reuseFailAlloc_1403_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1399_);
                    lean_del_object(v___x_1396_);
                    v___x_1404_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0;
                    v___x_1405_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1;
                    v___x_1406_ = lean_unsigned_to_nat(81);
                    v___x_1407_ = lean_unsigned_to_nat(41);
                    v___x_1408_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2;
                    v___x_1409_ = 1;
                    v___x_1410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_c_1390_,
                        v___x_1409_,
                    );
                    v___x_1411_ = lean_string_append(v___x_1408_, v___x_1410_);
                    lean_dec_ref(v___x_1410_);
                    v___x_1412_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3;
                    v___x_1413_ = lean_string_append(v___x_1411_, v___x_1412_);
                    v___x_1414_ = l_mkPanicMessageWithDecl(
                        v___x_1404_,
                        v___x_1405_,
                        v___x_1406_,
                        v___x_1407_,
                        v___x_1413_,
                    );
                    lean_dec_ref(v___x_1413_);
                    v___x_1415_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(v___x_1414_, v_a_1391_, v_snd_1394_);
                    return v___x_1415_;
                }
            }
            2 => {
                return v___x_1402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___boxed(
    mut v_extFind_x3f_1418_: *mut LeanObject,
    mut v_c_1419_: *mut LeanObject,
    mut v_a_1420_: *mut LeanObject,
    mut v_a_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1422_: *mut LeanObject = core::ptr::null_mut();
    v_res_1422_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(
        v_extFind_x3f_1418_,
        v_c_1419_,
        v_a_1420_,
        v_a_1421_,
    );
    lean_dec_ref(v_a_1420_);
    return v_res_1422_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(
    mut v_a_1426_: *mut LeanObject,
    mut v_b_1427_: *mut LeanObject,
) -> u8 {
    let mut v_fst_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: u8 = 0;
    v_fst_1428_ = lean_ctor_get(v_a_1426_, 0);
    v_fst_1429_ = lean_ctor_get(v_b_1427_, 0);
    v___x_1430_ = l_Lean_Name_quickLt(v_fst_1428_, v_fst_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0___boxed(
    mut v_a_1431_: *mut LeanObject,
    mut v_b_1432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1433_: u8 = 0;
    let mut v_r_1434_: *mut LeanObject = core::ptr::null_mut();
    v_res_1433_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_1431_, v_b_1432_);
    lean_dec_ref(v_b_1432_);
    lean_dec_ref(v_a_1431_);
    v_r_1434_ = lean_box((v_res_1433_) as usize);
    return v_r_1434_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(
    mut v_as_1435_: *mut LeanObject,
    mut v_k_1436_: *mut LeanObject,
    mut v_x_1437_: *mut LeanObject,
    mut v_x_1438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: u8 = 0;
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1439_ = lean_nat_add(v_x_1437_, v_x_1438_);
                v___x_1440_ = lean_unsigned_to_nat(1);
                v_m_1441_ = lean_nat_shiftr(v___x_1439_, v___x_1440_);
                lean_dec(v___x_1439_);
                v_a_1442_ = lean_array_fget_borrowed(v_as_1435_, v_m_1441_);
                v___x_1443_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_1442_, v_k_1436_);
                if v___x_1443_ == 0 {
                    lean_dec(v_x_1438_);
                    v___x_1444_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_k_1436_, v_a_1442_);
                    if v___x_1444_ == 0 {
                        lean_dec(v_m_1441_);
                        lean_dec(v_x_1437_);
                        lean_inc(v_a_1442_);
                        v___x_1445_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1445_, 0, v_a_1442_);
                        return v___x_1445_;
                    } else {
                        v___x_1446_ = lean_unsigned_to_nat(0);
                        v___x_1447_ = lean_nat_dec_eq(v_m_1441_, v___x_1446_);
                        if v___x_1447_ == 0 {
                            v___x_1448_ = lean_nat_sub(v_m_1441_, v___x_1440_);
                            lean_dec(v_m_1441_);
                            v___x_1449_ = lean_nat_dec_lt(v___x_1448_, v_x_1437_);
                            if v___x_1449_ == 0 {
                                v_x_1438_ = v___x_1448_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v___x_1448_);
                                lean_dec(v_x_1437_);
                                v___x_1451_ = lean_box(0);
                                return v___x_1451_;
                            }
                        } else {
                            lean_dec(v_m_1441_);
                            lean_dec(v_x_1437_);
                            v___x_1452_ = lean_box(0);
                            return v___x_1452_;
                        }
                    }
                } else {
                    lean_dec(v_x_1437_);
                    v___x_1453_ = lean_nat_add(v_m_1441_, v___x_1440_);
                    lean_dec(v_m_1441_);
                    v___x_1454_ = lean_nat_dec_le(v___x_1453_, v_x_1438_);
                    if v___x_1454_ == 0 {
                        lean_dec(v___x_1453_);
                        lean_dec(v_x_1438_);
                        v___x_1455_ = lean_box(0);
                        return v___x_1455_;
                    } else {
                        v_x_1437_ = v___x_1453_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___boxed(
    mut v_as_1457_: *mut LeanObject,
    mut v_k_1458_: *mut LeanObject,
    mut v_x_1459_: *mut LeanObject,
    mut v_x_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1461_: *mut LeanObject = core::ptr::null_mut();
    v_res_1461_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v_as_1457_, v_k_1458_, v_x_1459_, v_x_1460_);
    lean_dec_ref(v_k_1458_);
    lean_dec_ref(v_as_1457_);
    return v_res_1461_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(
    mut v_s_1462_: *mut LeanObject,
    mut v_env_1463_: *mut LeanObject,
    mut v_c_1464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v_snd_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1465_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1463_, v_c_1464_);
                if lean_obj_tag(v___x_1465_) == 0 {
                    lean_dec(v_c_1464_);
                    v___x_1466_ = lean_box(0);
                    return v___x_1466_;
                } else {
                    v_val_1467_ = lean_ctor_get(v___x_1465_, 0);
                    lean_inc(v_val_1467_);
                    lean_dec_ref_known(v___x_1465_, 1);
                    v___x_1468_ = lean_array_get_size(v_s_1462_);
                    v___x_1469_ = lean_nat_dec_lt(v_val_1467_, v___x_1468_);
                    if v___x_1469_ == 0 {
                        lean_dec(v_val_1467_);
                        lean_dec(v_c_1464_);
                        v___x_1470_ = lean_box(0);
                        return v___x_1470_;
                    } else {
                        v___x_1471_ = lean_array_fget_borrowed(v_s_1462_, v_val_1467_);
                        lean_dec(v_val_1467_);
                        v___x_1472_ = lean_unsigned_to_nat(0);
                        v___x_1473_ = lean_array_get_size(v___x_1471_);
                        v___x_1474_ = lean_nat_dec_lt(v___x_1472_, v___x_1473_);
                        if v___x_1474_ == 0 {
                            lean_dec(v_c_1464_);
                            v___x_1475_ = lean_box(0);
                            return v___x_1475_;
                        } else {
                            v___x_1476_ = lean_unsigned_to_nat(1);
                            v___x_1477_ = lean_nat_sub(v___x_1473_, v___x_1476_);
                            v___x_1478_ = lean_nat_dec_le(v___x_1472_, v___x_1477_);
                            if v___x_1478_ == 0 {
                                lean_dec(v___x_1477_);
                                lean_dec(v_c_1464_);
                                v___x_1479_ = lean_box(0);
                                return v___x_1479_;
                            } else {
                                v___x_1480_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0;
                                v___x_1481_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_1481_, 0, v_c_1464_);
                                lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                                v___x_1482_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v___x_1471_, v___x_1481_, v___x_1472_, v___x_1477_);
                                lean_dec_ref_known(v___x_1481_, 2);
                                if lean_obj_tag(v___x_1482_) == 0 {
                                    v___x_1483_ = lean_box(0);
                                    return v___x_1483_;
                                } else {
                                    v_val_1484_ = lean_ctor_get(v___x_1482_, 0);
                                    v_isSharedCheck_1492_ = (!lean_is_exclusive(v___x_1482_)) as u8;
                                    if v_isSharedCheck_1492_ == 0 {
                                        v___x_1486_ = v___x_1482_;
                                        v_isShared_1487_ = v_isSharedCheck_1492_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_val_1484_);
                                        lean_dec(v___x_1482_);
                                        v___x_1486_ = lean_box(0);
                                        v_isShared_1487_ = v_isSharedCheck_1492_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v_snd_1488_ = lean_ctor_get(v_val_1484_, 1);
                lean_inc(v_snd_1488_);
                lean_dec(v_val_1484_);
                if v_isShared_1487_ == 0 {
                    lean_ctor_set(v___x_1486_, 0, v_snd_1488_);
                    v___x_1490_ = v___x_1486_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_snd_1488_);
                    v___x_1490_ = v_reuseFailAlloc_1491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed(
    mut v_s_1493_: *mut LeanObject,
    mut v_env_1494_: *mut LeanObject,
    mut v_c_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1496_: *mut LeanObject = core::ptr::null_mut();
    v_res_1496_ = l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(
        v_s_1493_,
        v_env_1494_,
        v_c_1495_,
    );
    lean_dec_ref(v_env_1494_);
    lean_dec_ref(v_s_1493_);
    return v_res_1496_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(
    mut v_as_1497_: *mut LeanObject,
    mut v_k_1498_: *mut LeanObject,
    mut v_x_1499_: *mut LeanObject,
    mut v_x_1500_: *mut LeanObject,
    mut v_x_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v_as_1497_, v_k_1498_, v_x_1499_, v_x_1500_);
    return v___x_1502_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___boxed(
    mut v_as_1503_: *mut LeanObject,
    mut v_k_1504_: *mut LeanObject,
    mut v_x_1505_: *mut LeanObject,
    mut v_x_1506_: *mut LeanObject,
    mut v_x_1507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1508_: *mut LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(v_as_1503_, v_k_1504_, v_x_1505_, v_x_1506_, v_x_1507_);
    lean_dec_ref(v_k_1504_);
    lean_dec_ref(v_as_1503_);
    return v_res_1508_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_x_1511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    v___x_1512_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_;
    return v___x_1512_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_x_1513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1514_: *mut LeanObject = core::ptr::null_mut();
    v_res_1514_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_x_1513_);
    lean_dec_ref(v_x_1513_);
    return v_res_1514_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_x_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    v___x_1516_ = lean_box(0);
    return v___x_1516_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_x_1517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1518_: *mut LeanObject = core::ptr::null_mut();
    v_res_1518_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_x_1517_);
    lean_dec_ref(v_x_1517_);
    return v_res_1518_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_s_1519_: *mut LeanObject,
    mut v_x_1520_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_s_1519_);
    return v_s_1519_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_s_1521_: *mut LeanObject,
    mut v_x_1522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1523_: *mut LeanObject = core::ptr::null_mut();
    v_res_1523_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_s_1521_, v_x_1522_);
    lean_dec_ref(v_x_1522_);
    lean_dec_ref(v_s_1521_);
    return v_res_1523_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_importedEntries_1524_: *mut LeanObject,
    mut v___y_1525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    v___x_1527_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1527_, 0, v_importedEntries_1524_);
    return v___x_1527_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_importedEntries_1528_: *mut LeanObject,
    mut v___y_1529_: *mut LeanObject,
    mut v___y_1530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1531_: *mut LeanObject = core::ptr::null_mut();
    v_res_1531_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_importedEntries_1528_, v___y_1529_);
    lean_dec_ref(v___y_1529_);
    return v_res_1531_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_exportedEnv_1532_: *mut LeanObject,
    mut v___x_1533_: u8,
    mut v_names_1534_: *mut LeanObject,
    mut v_name_1535_: *mut LeanObject,
    mut v_x_1536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_name_1535_);
    v___x_1537_ = l_Lean_Environment_find_x3f(v_exportedEnv_1532_, v_name_1535_, v___x_1533_);
    if lean_obj_tag(v___x_1537_) == 0 {
        lean_dec(v_name_1535_);
        return v_names_1534_;
    } else {
        let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_1537_, 1);
        v___x_1538_ = lean_array_push(v_names_1534_, v_name_1535_);
        return v___x_1538_;
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_exportedEnv_1539_: *mut LeanObject,
    mut v___x_1540_: *mut LeanObject,
    mut v_names_1541_: *mut LeanObject,
    mut v_name_1542_: *mut LeanObject,
    mut v_x_1543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1738__boxed_1544_: u8 = 0;
    let mut v_res_1545_: *mut LeanObject = core::ptr::null_mut();
    v___x_1738__boxed_1544_ = (lean_unbox(v___x_1540_) as u8);
    v_res_1545_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_exportedEnv_1539_, v___x_1738__boxed_1544_, v_names_1541_, v_name_1542_, v_x_1543_);
    lean_dec_ref(v_x_1543_);
    return v_res_1545_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__1(
    mut v_s_1546_: *mut LeanObject,
    mut v_sz_1547_: usize,
    mut v_i_1548_: usize,
    mut v_bs_1549_: *mut LeanObject,
    mut v___y_1550_: *mut LeanObject,
    mut v___y_1551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1561_: u8 = 0;
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: usize = 0;
    let mut v___x_1567_: usize = 0;
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1552_ = lean_usize_dec_lt(v_i_1548_, v_sz_1547_);
                if v___x_1552_ == 0 {
                    lean_dec_ref(v_s_1546_);
                    v___x_1553_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1553_, 0, v_bs_1549_);
                    lean_ctor_set(v___x_1553_, 1, v___y_1551_);
                    return v___x_1553_;
                } else {
                    v_v_1554_ = lean_array_uget(v_bs_1549_, v_i_1548_);
                    lean_inc_ref(v_s_1546_);
                    v___x_1555_ = lean_alloc_closure(l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed as *mut core::ffi::c_void, 3, 1);
                    lean_closure_set(v___x_1555_, 0, v_s_1546_);
                    lean_inc(v_v_1554_);
                    v___x_1556_ =
                        l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(
                            v___x_1555_,
                            v_v_1554_,
                            v___y_1550_,
                            v___y_1551_,
                        );
                    v_fst_1557_ = lean_ctor_get(v___x_1556_, 0);
                    v_snd_1558_ = lean_ctor_get(v___x_1556_, 1);
                    v_isSharedCheck_1571_ = (!lean_is_exclusive(v___x_1556_)) as u8;
                    if v_isSharedCheck_1571_ == 0 {
                        v___x_1560_ = v___x_1556_;
                        v_isShared_1561_ = v_isSharedCheck_1571_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1558_);
                        lean_inc(v_fst_1557_);
                        lean_dec(v___x_1556_);
                        v___x_1560_ = lean_box(0);
                        v_isShared_1561_ = v_isSharedCheck_1571_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1562_ = lean_unsigned_to_nat(0);
                v_bs_x27_1563_ = lean_array_uset(v_bs_1549_, v_i_1548_, v___x_1562_);
                if v_isShared_1561_ == 0 {
                    lean_ctor_set(v___x_1560_, 1, v_fst_1557_);
                    lean_ctor_set(v___x_1560_, 0, v_v_1554_);
                    v___x_1565_ = v___x_1560_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_v_1554_);
                    lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_fst_1557_);
                    v___x_1565_ = v_reuseFailAlloc_1570_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1566_ = 1usize;
                v___x_1567_ = lean_usize_add(v_i_1548_, v___x_1566_);
                v___x_1568_ = lean_array_uset(v_bs_x27_1563_, v_i_1548_, v___x_1565_);
                v_i_1548_ = v___x_1567_;
                v_bs_1549_ = v___x_1568_;
                v___y_1551_ = v_snd_1558_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__1___boxed(
    mut v_s_1572_: *mut LeanObject,
    mut v_sz_1573_: *mut LeanObject,
    mut v_i_1574_: *mut LeanObject,
    mut v_bs_1575_: *mut LeanObject,
    mut v___y_1576_: *mut LeanObject,
    mut v___y_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1578_: usize = 0;
    let mut v_i_boxed_1579_: usize = 0;
    let mut v_res_1580_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1578_ = lean_unbox_usize(v_sz_1573_);
    lean_dec(v_sz_1573_);
    v_i_boxed_1579_ = lean_unbox_usize(v_i_1574_);
    lean_dec(v_i_1574_);
    v_res_1580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__1(v_s_1572_, v_sz_boxed_1578_, v_i_boxed_1579_, v_bs_1575_, v___y_1576_, v___y_1577_);
    lean_dec_ref(v___y_1576_);
    return v_res_1580_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_f_1581_: *mut LeanObject,
    mut v_keys_1582_: *mut LeanObject,
    mut v_vals_1583_: *mut LeanObject,
    mut v_i_1584_: *mut LeanObject,
    mut v_acc_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    let mut v_k_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1586_ = lean_array_get_size(v_keys_1582_);
                v___x_1587_ = lean_nat_dec_lt(v_i_1584_, v___x_1586_);
                if v___x_1587_ == 0 {
                    lean_dec(v_i_1584_);
                    lean_dec(v_f_1581_);
                    return v_acc_1585_;
                } else {
                    v_k_1588_ = lean_array_fget_borrowed(v_keys_1582_, v_i_1584_);
                    v_v_1589_ = lean_array_fget_borrowed(v_vals_1583_, v_i_1584_);
                    lean_inc(v_f_1581_);
                    lean_inc(v_v_1589_);
                    lean_inc(v_k_1588_);
                    v___x_1590_ = lean_apply_3(v_f_1581_, v_acc_1585_, v_k_1588_, v_v_1589_);
                    v___x_1591_ = lean_unsigned_to_nat(1);
                    v___x_1592_ = lean_nat_add(v_i_1584_, v___x_1591_);
                    lean_dec(v_i_1584_);
                    v_i_1584_ = v___x_1592_;
                    v_acc_1585_ = v___x_1590_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_f_1594_: *mut LeanObject,
    mut v_keys_1595_: *mut LeanObject,
    mut v_vals_1596_: *mut LeanObject,
    mut v_i_1597_: *mut LeanObject,
    mut v_acc_1598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1599_: *mut LeanObject = core::ptr::null_mut();
    v_res_1599_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_1594_, v_keys_1595_, v_vals_1596_, v_i_1597_, v_acc_1598_);
    lean_dec_ref(v_vals_1596_);
    lean_dec_ref(v_keys_1595_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_f_1600_: *mut LeanObject,
    mut v_x_1601_: *mut LeanObject,
    mut v_x_1602_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1601_) == 0 {
        let mut v_es_1603_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: u8 = 0;
        v_es_1603_ = lean_ctor_get(v_x_1601_, 0);
        v___x_1604_ = lean_unsigned_to_nat(0);
        v___x_1605_ = lean_array_get_size(v_es_1603_);
        v___x_1606_ = lean_nat_dec_lt(v___x_1604_, v___x_1605_);
        if v___x_1606_ == 0 {
            lean_dec(v_f_1600_);
            return v_x_1602_;
        } else {
            let mut v___x_1607_: u8 = 0;
            v___x_1607_ = lean_nat_dec_le(v___x_1605_, v___x_1605_);
            if v___x_1607_ == 0 {
                if v___x_1606_ == 0 {
                    lean_dec(v_f_1600_);
                    return v_x_1602_;
                } else {
                    let mut v___x_1608_: usize = 0;
                    let mut v___x_1609_: usize = 0;
                    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
                    v___x_1608_ = 0usize;
                    v___x_1609_ = lean_usize_of_nat(v___x_1605_);
                    v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1600_, v_es_1603_, v___x_1608_, v___x_1609_, v_x_1602_);
                    return v___x_1610_;
                }
            } else {
                let mut v___x_1611_: usize = 0;
                let mut v___x_1612_: usize = 0;
                let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
                v___x_1611_ = 0usize;
                v___x_1612_ = lean_usize_of_nat(v___x_1605_);
                v___x_1613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1600_, v_es_1603_, v___x_1611_, v___x_1612_, v_x_1602_);
                return v___x_1613_;
            }
        }
    } else {
        let mut v_ks_1614_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_1615_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
        v_ks_1614_ = lean_ctor_get(v_x_1601_, 0);
        v_vs_1615_ = lean_ctor_get(v_x_1601_, 1);
        v___x_1616_ = lean_unsigned_to_nat(0);
        v___x_1617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_1600_, v_ks_1614_, v_vs_1615_, v___x_1616_, v_x_1602_);
        return v___x_1617_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_f_1618_: *mut LeanObject,
    mut v_as_1619_: *mut LeanObject,
    mut v_i_1620_: usize,
    mut v_stop_1621_: usize,
    mut v_b_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: usize = 0;
    let mut v___x_1626_: usize = 0;
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1628_ = lean_usize_dec_eq(v_i_1620_, v_stop_1621_);
                if v___x_1628_ == 0 {
                    v___x_1629_ = lean_array_uget_borrowed(v_as_1619_, v_i_1620_);
                    match lean_obj_tag(v___x_1629_) {
                        0 => {
                            v_key_1630_ = lean_ctor_get(v___x_1629_, 0);
                            v_val_1631_ = lean_ctor_get(v___x_1629_, 1);
                            lean_inc(v_f_1618_);
                            lean_inc(v_val_1631_);
                            lean_inc(v_key_1630_);
                            v___x_1632_ =
                                lean_apply_3(v_f_1618_, v_b_1622_, v_key_1630_, v_val_1631_);
                            v___y_1624_ = v___x_1632_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_1633_ = lean_ctor_get(v___x_1629_, 0);
                            lean_inc(v_f_1618_);
                            v___x_1634_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1618_, v_node_1633_, v_b_1622_);
                            v___y_1624_ = v___x_1634_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_1624_ = v_b_1622_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_f_1618_);
                    return v_b_1622_;
                }
            }
            1 => {
                v___x_1625_ = 1usize;
                v___x_1626_ = lean_usize_add(v_i_1620_, v___x_1625_);
                v_i_1620_ = v___x_1626_;
                v_b_1622_ = v___y_1624_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_f_1635_: *mut LeanObject,
    mut v_as_1636_: *mut LeanObject,
    mut v_i_1637_: *mut LeanObject,
    mut v_stop_1638_: *mut LeanObject,
    mut v_b_1639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1640_: usize = 0;
    let mut v_stop_boxed_1641_: usize = 0;
    let mut v_res_1642_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1640_ = lean_unbox_usize(v_i_1637_);
    lean_dec(v_i_1637_);
    v_stop_boxed_1641_ = lean_unbox_usize(v_stop_1638_);
    lean_dec(v_stop_1638_);
    v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1635_, v_as_1636_, v_i_boxed_1640_, v_stop_boxed_1641_, v_b_1639_);
    lean_dec_ref(v_as_1636_);
    return v_res_1642_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_1643_: *mut LeanObject,
    mut v_x_1644_: *mut LeanObject,
    mut v_x_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1646_: *mut LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1643_, v_x_1644_, v_x_1645_);
    lean_dec_ref(v_x_1644_);
    return v_res_1646_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg___lam__0(
    mut v_f_1647_: *mut LeanObject,
    mut v_x1_1648_: *mut LeanObject,
    mut v_x2_1649_: *mut LeanObject,
    mut v_x3_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    v___x_1651_ = lean_apply_3(v_f_1647_, v_x1_1648_, v_x2_1649_, v_x3_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(
    mut v_map_1652_: *mut LeanObject,
    mut v_f_1653_: *mut LeanObject,
    mut v_init_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    v___f_1655_ = lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    lean_closure_set(v___f_1655_, 0, v_f_1653_);
    v___x_1656_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_1655_, v_map_1652_, v_init_1654_);
    return v___x_1656_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_map_1657_: *mut LeanObject,
    mut v_f_1658_: *mut LeanObject,
    mut v_init_1659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1660_: *mut LeanObject = core::ptr::null_mut();
    v_res_1660_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(v_map_1657_, v_f_1658_, v_init_1659_);
    lean_dec_ref(v_map_1657_);
    return v_res_1660_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(
    mut v_hi_1661_: *mut LeanObject,
    mut v_pivot_1662_: *mut LeanObject,
    mut v_as_1663_: *mut LeanObject,
    mut v_i_1664_: *mut LeanObject,
    mut v_k_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1666_ = lean_nat_dec_lt(v_k_1665_, v_hi_1661_);
                if v___x_1666_ == 0 {
                    lean_dec(v_k_1665_);
                    v___x_1667_ = lean_array_fswap(v_as_1663_, v_i_1664_, v_hi_1661_);
                    v___x_1668_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1668_, 0, v_i_1664_);
                    lean_ctor_set(v___x_1668_, 1, v___x_1667_);
                    return v___x_1668_;
                } else {
                    v___x_1669_ = lean_array_fget_borrowed(v_as_1663_, v_k_1665_);
                    v_fst_1670_ = lean_ctor_get(v___x_1669_, 0);
                    v_fst_1671_ = lean_ctor_get(v_pivot_1662_, 0);
                    v___x_1672_ = l_Lean_Name_quickLt(v_fst_1670_, v_fst_1671_);
                    if v___x_1672_ == 0 {
                        v___x_1673_ = lean_unsigned_to_nat(1);
                        v___x_1674_ = lean_nat_add(v_k_1665_, v___x_1673_);
                        lean_dec(v_k_1665_);
                        v_k_1665_ = v___x_1674_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1676_ = lean_array_fswap(v_as_1663_, v_i_1664_, v_k_1665_);
                        v___x_1677_ = lean_unsigned_to_nat(1);
                        v___x_1678_ = lean_nat_add(v_i_1664_, v___x_1677_);
                        lean_dec(v_i_1664_);
                        v___x_1679_ = lean_nat_add(v_k_1665_, v___x_1677_);
                        lean_dec(v_k_1665_);
                        v_as_1663_ = v___x_1676_;
                        v_i_1664_ = v___x_1678_;
                        v_k_1665_ = v___x_1679_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(
    mut v_hi_1681_: *mut LeanObject,
    mut v_pivot_1682_: *mut LeanObject,
    mut v_as_1683_: *mut LeanObject,
    mut v_i_1684_: *mut LeanObject,
    mut v_k_1685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1686_: *mut LeanObject = core::ptr::null_mut();
    v_res_1686_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_1681_, v_pivot_1682_, v_as_1683_, v_i_1684_, v_k_1685_);
    lean_dec_ref(v_pivot_1682_);
    lean_dec(v_hi_1681_);
    return v_res_1686_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(
    mut v_n_1687_: *mut LeanObject,
    mut v_as_1688_: *mut LeanObject,
    mut v_lo_1689_: *mut LeanObject,
    mut v_hi_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: u8 = 0;
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1702_ = lean_nat_dec_lt(v_lo_1689_, v_hi_1690_);
                if v___x_1702_ == 0 {
                    lean_dec(v_lo_1689_);
                    return v_as_1688_;
                } else {
                    v___x_1703_ = lean_nat_add(v_lo_1689_, v_hi_1690_);
                    v___x_1704_ = lean_unsigned_to_nat(1);
                    v_mid_1705_ = lean_nat_shiftr(v___x_1703_, v___x_1704_);
                    lean_dec(v___x_1703_);
                    v___x_1718_ = lean_array_fget_borrowed(v_as_1688_, v_mid_1705_);
                    v___x_1719_ = lean_array_fget_borrowed(v_as_1688_, v_lo_1689_);
                    v___x_1720_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_1718_, v___x_1719_);
                    if v___x_1720_ == 0 {
                        v___y_1713_ = v_as_1688_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1721_ = lean_array_fswap(v_as_1688_, v_lo_1689_, v_mid_1705_);
                        v___y_1713_ = v___x_1721_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1693_ = lean_array_fget(v___y_1692_, v_hi_1690_);
                lean_inc_n(v_lo_1689_, 2);
                v___x_1694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_1690_, v_pivot_1693_, v___y_1692_, v_lo_1689_, v_lo_1689_);
                lean_dec(v_pivot_1693_);
                v_fst_1695_ = lean_ctor_get(v___x_1694_, 0);
                lean_inc(v_fst_1695_);
                v_snd_1696_ = lean_ctor_get(v___x_1694_, 1);
                lean_inc(v_snd_1696_);
                lean_dec_ref(v___x_1694_);
                v___x_1697_ = lean_nat_dec_le(v_hi_1690_, v_fst_1695_);
                if v___x_1697_ == 0 {
                    v___x_1698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v_n_1687_, v_snd_1696_, v_lo_1689_, v_fst_1695_);
                    v___x_1699_ = lean_unsigned_to_nat(1);
                    v___x_1700_ = lean_nat_add(v_fst_1695_, v___x_1699_);
                    lean_dec(v_fst_1695_);
                    v_as_1688_ = v___x_1698_;
                    v_lo_1689_ = v___x_1700_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_1695_);
                    lean_dec(v_lo_1689_);
                    return v_snd_1696_;
                }
            }
            2 => {
                v___x_1708_ = lean_array_fget_borrowed(v___y_1707_, v_mid_1705_);
                v___x_1709_ = lean_array_fget_borrowed(v___y_1707_, v_hi_1690_);
                v___x_1710_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_1708_, v___x_1709_);
                if v___x_1710_ == 0 {
                    lean_dec(v_mid_1705_);
                    v___y_1692_ = v___y_1707_;
                    state = 1;
                    continue;
                } else {
                    v___x_1711_ = lean_array_fswap(v___y_1707_, v_mid_1705_, v_hi_1690_);
                    lean_dec(v_mid_1705_);
                    v___y_1692_ = v___x_1711_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1714_ = lean_array_fget_borrowed(v___y_1713_, v_hi_1690_);
                v___x_1715_ = lean_array_fget_borrowed(v___y_1713_, v_lo_1689_);
                v___x_1716_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_1714_, v___x_1715_);
                if v___x_1716_ == 0 {
                    v___y_1707_ = v___y_1713_;
                    state = 2;
                    continue;
                } else {
                    v___x_1717_ = lean_array_fswap(v___y_1713_, v_lo_1689_, v_hi_1690_);
                    v___y_1707_ = v___x_1717_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg___boxed(
    mut v_n_1722_: *mut LeanObject,
    mut v_as_1723_: *mut LeanObject,
    mut v_lo_1724_: *mut LeanObject,
    mut v_hi_1725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1726_: *mut LeanObject = core::ptr::null_mut();
    v_res_1726_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v_n_1722_, v_as_1723_, v_lo_1724_, v_hi_1725_);
    lean_dec(v_hi_1725_);
    lean_dec(v_n_1722_);
    return v_res_1726_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v___x_1729_: *mut LeanObject,
    mut v_env_1730_: *mut LeanObject,
    mut v_s_1731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_checked_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_constants_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v_exportedEnv_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_privateEnv_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allNames_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1744_: usize = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entries_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: u8 = 0;
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_checked_1732_ = lean_ctor_get(v_env_1730_, 2);
                lean_inc_ref(v_checked_1732_);
                v___x_1733_ = lean_task_get_own(v_checked_1732_);
                v_constants_1734_ = lean_ctor_get(v___x_1733_, 0);
                lean_inc_ref(v_constants_1734_);
                lean_dec(v___x_1733_);
                v_map_u2082_1735_ = lean_ctor_get(v_constants_1734_, 1);
                lean_inc_ref(v_map_u2082_1735_);
                lean_dec_ref(v_constants_1734_);
                v___x_1736_ = 1;
                lean_inc_ref(v_env_1730_);
                v_exportedEnv_1737_ = l_Lean_Environment_setExporting(v_env_1730_, v___x_1736_);
                v___x_1738_ = 0;
                v___x_1739_ = lean_box((v___x_1738_) as usize);
                v___f_1740_ = lean_alloc_closure(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 5, 2);
                lean_closure_set(v___f_1740_, 0, v_exportedEnv_1737_);
                lean_closure_set(v___f_1740_, 1, v___x_1739_);
                v_privateEnv_1741_ = l_Lean_Environment_setExporting(v_env_1730_, v___x_1738_);
                v___x_1742_ = lean_mk_empty_array_with_capacity(v___x_1729_);
                v_allNames_1743_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(v_map_u2082_1735_, v___f_1740_, v___x_1742_);
                lean_dec_ref(v_map_u2082_1735_);
                v_sz_1744_ = lean_array_size(v_allNames_1743_);
                v___x_1745_ = lean_box_usize(v_sz_1744_);
                v___x_1746_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_;
                v___x_1747_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__1___boxed as *mut core::ffi::c_void, 6, 4);
                lean_closure_set(v___x_1747_, 0, v_s_1731_);
                lean_closure_set(v___x_1747_, 1, v___x_1745_);
                lean_closure_set(v___x_1747_, 2, v___x_1746_);
                lean_closure_set(v___x_1747_, 3, v_allNames_1743_);
                v_entries_1748_ =
                    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
                        v_privateEnv_1741_,
                        v___x_1747_,
                    );
                v___x_1749_ = lean_array_get_size(v_entries_1748_);
                v___x_1755_ = lean_nat_dec_eq(v___x_1749_, v___x_1729_);
                if v___x_1755_ == 0 {
                    v___x_1756_ = lean_unsigned_to_nat(1);
                    v___x_1757_ = lean_nat_sub(v___x_1749_, v___x_1756_);
                    v___x_1761_ = lean_nat_dec_le(v___x_1729_, v___x_1757_);
                    if v___x_1761_ == 0 {
                        lean_dec(v___x_1729_);
                        lean_inc(v___x_1757_);
                        v___y_1759_ = v___x_1757_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1759_ = v___x_1729_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1729_);
                    lean_inc_n(v_entries_1748_, 2);
                    v___x_1762_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1762_, 0, v_entries_1748_);
                    lean_ctor_set(v___x_1762_, 1, v_entries_1748_);
                    lean_ctor_set(v___x_1762_, 2, v_entries_1748_);
                    return v___x_1762_;
                }
            }
            1 => {
                v___x_1753_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v___x_1749_, v_entries_1748_, v___y_1751_, v___y_1752_);
                lean_dec(v___y_1752_);
                lean_inc_ref_n(v___x_1753_, 2);
                v___x_1754_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1754_, 0, v___x_1753_);
                lean_ctor_set(v___x_1754_, 1, v___x_1753_);
                lean_ctor_set(v___x_1754_, 2, v___x_1753_);
                return v___x_1754_;
            }
            2 => {
                v___x_1760_ = lean_nat_dec_le(v___y_1759_, v___x_1757_);
                if v___x_1760_ == 0 {
                    lean_dec(v___x_1757_);
                    lean_inc(v___y_1759_);
                    v___y_1751_ = v___y_1759_;
                    v___y_1752_ = v___y_1759_;
                    state = 1;
                    continue;
                } else {
                    v___y_1751_ = v___y_1759_;
                    v___y_1752_ = v___x_1757_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v___x_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    v___x_1765_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1765_, 0, v___x_1763_);
    return v___x_1765_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v___x_1766_: *mut LeanObject,
    mut v___y_1767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1768_: *mut LeanObject = core::ptr::null_mut();
    v_res_1768_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v___x_1766_);
    return v_res_1768_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    v___x_1816_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_;
    v___x_1817_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1816_);
    return v___x_1817_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_a_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1819_: *mut LeanObject = core::ptr::null_mut();
    v_res_1819_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_();
    return v_res_1819_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0(
    mut v_00_u03c3_1820_: *mut LeanObject,
    mut v_00_u03b2_1821_: *mut LeanObject,
    mut v_map_1822_: *mut LeanObject,
    mut v_f_1823_: *mut LeanObject,
    mut v_init_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(v_map_1822_, v_f_1823_, v_init_1824_);
    return v___x_1825_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03c3_1826_: *mut LeanObject,
    mut v_00_u03b2_1827_: *mut LeanObject,
    mut v_map_1828_: *mut LeanObject,
    mut v_f_1829_: *mut LeanObject,
    mut v_init_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1831_: *mut LeanObject = core::ptr::null_mut();
    v_res_1831_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0(v_00_u03c3_1826_, v_00_u03b2_1827_, v_map_1828_, v_f_1829_, v_init_1830_);
    lean_dec_ref(v_map_1828_);
    return v_res_1831_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2(
    mut v_n_1832_: *mut LeanObject,
    mut v_as_1833_: *mut LeanObject,
    mut v_lo_1834_: *mut LeanObject,
    mut v_hi_1835_: *mut LeanObject,
    mut v_w_1836_: *mut LeanObject,
    mut v_hlo_1837_: *mut LeanObject,
    mut v_hhi_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    v___x_1839_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v_n_1832_, v_as_1833_, v_lo_1834_, v_hi_1835_);
    return v___x_1839_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___boxed(
    mut v_n_1840_: *mut LeanObject,
    mut v_as_1841_: *mut LeanObject,
    mut v_lo_1842_: *mut LeanObject,
    mut v_hi_1843_: *mut LeanObject,
    mut v_w_1844_: *mut LeanObject,
    mut v_hlo_1845_: *mut LeanObject,
    mut v_hhi_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1847_: *mut LeanObject = core::ptr::null_mut();
    v_res_1847_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2(v_n_1840_, v_as_1841_, v_lo_1842_, v_hi_1843_, v_w_1844_, v_hlo_1845_, v_hhi_1846_);
    lean_dec(v_hi_1843_);
    lean_dec(v_n_1840_);
    return v_res_1847_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_map_1848_: *mut LeanObject,
    mut v_f_1849_: *mut LeanObject,
    mut v_init_1850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    v___x_1851_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1849_, v_map_1848_, v_init_1850_);
    return v___x_1851_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_map_1852_: *mut LeanObject,
    mut v_f_1853_: *mut LeanObject,
    mut v_init_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1855_: *mut LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_1852_, v_f_1853_, v_init_1854_);
    lean_dec_ref(v_map_1852_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03c3_1856_: *mut LeanObject,
    mut v_00_u03b2_1857_: *mut LeanObject,
    mut v_map_1858_: *mut LeanObject,
    mut v_f_1859_: *mut LeanObject,
    mut v_init_1860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    v___x_1861_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1859_, v_map_1858_, v_init_1860_);
    return v___x_1861_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03c3_1862_: *mut LeanObject,
    mut v_00_u03b2_1863_: *mut LeanObject,
    mut v_map_1864_: *mut LeanObject,
    mut v_f_1865_: *mut LeanObject,
    mut v_init_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1867_: *mut LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_1862_, v_00_u03b2_1863_, v_map_1864_, v_f_1865_, v_init_1866_);
    lean_dec_ref(v_map_1864_);
    return v_res_1867_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3(
    mut v_n_1868_: *mut LeanObject,
    mut v_lo_1869_: *mut LeanObject,
    mut v_hi_1870_: *mut LeanObject,
    mut v_hhi_1871_: *mut LeanObject,
    mut v_pivot_1872_: *mut LeanObject,
    mut v_as_1873_: *mut LeanObject,
    mut v_i_1874_: *mut LeanObject,
    mut v_k_1875_: *mut LeanObject,
    mut v_ilo_1876_: *mut LeanObject,
    mut v_ik_1877_: *mut LeanObject,
    mut v_w_1878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    v___x_1879_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_1870_, v_pivot_1872_, v_as_1873_, v_i_1874_, v_k_1875_);
    return v___x_1879_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___boxed(
    mut v_n_1880_: *mut LeanObject,
    mut v_lo_1881_: *mut LeanObject,
    mut v_hi_1882_: *mut LeanObject,
    mut v_hhi_1883_: *mut LeanObject,
    mut v_pivot_1884_: *mut LeanObject,
    mut v_as_1885_: *mut LeanObject,
    mut v_i_1886_: *mut LeanObject,
    mut v_k_1887_: *mut LeanObject,
    mut v_ilo_1888_: *mut LeanObject,
    mut v_ik_1889_: *mut LeanObject,
    mut v_w_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1891_: *mut LeanObject = core::ptr::null_mut();
    v_res_1891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3(v_n_1880_, v_lo_1881_, v_hi_1882_, v_hhi_1883_, v_pivot_1884_, v_as_1885_, v_i_1886_, v_k_1887_, v_ilo_1888_, v_ik_1889_, v_w_1890_);
    lean_dec_ref(v_pivot_1884_);
    lean_dec(v_hi_1882_);
    lean_dec(v_lo_1881_);
    lean_dec(v_n_1880_);
    return v_res_1891_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03c3_1892_: *mut LeanObject,
    mut v_00_u03b1_1893_: *mut LeanObject,
    mut v_00_u03b2_1894_: *mut LeanObject,
    mut v_f_1895_: *mut LeanObject,
    mut v_x_1896_: *mut LeanObject,
    mut v_x_1897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1895_, v_x_1896_, v_x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_1899_: *mut LeanObject,
    mut v_00_u03b1_1900_: *mut LeanObject,
    mut v_00_u03b2_1901_: *mut LeanObject,
    mut v_f_1902_: *mut LeanObject,
    mut v_x_1903_: *mut LeanObject,
    mut v_x_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1905_: *mut LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_1899_, v_00_u03b1_1900_, v_00_u03b2_1901_, v_f_1902_, v_x_1903_, v_x_1904_);
    lean_dec_ref(v_x_1903_);
    return v_res_1905_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1906_: *mut LeanObject,
    mut v_00_u03b2_1907_: *mut LeanObject,
    mut v_00_u03c3_1908_: *mut LeanObject,
    mut v_f_1909_: *mut LeanObject,
    mut v_as_1910_: *mut LeanObject,
    mut v_i_1911_: usize,
    mut v_stop_1912_: usize,
    mut v_b_1913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1909_, v_as_1910_, v_i_1911_, v_stop_1912_, v_b_1913_);
    return v___x_1914_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1915_: *mut LeanObject,
    mut v_00_u03b2_1916_: *mut LeanObject,
    mut v_00_u03c3_1917_: *mut LeanObject,
    mut v_f_1918_: *mut LeanObject,
    mut v_as_1919_: *mut LeanObject,
    mut v_i_1920_: *mut LeanObject,
    mut v_stop_1921_: *mut LeanObject,
    mut v_b_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1923_: usize = 0;
    let mut v_stop_boxed_1924_: usize = 0;
    let mut v_res_1925_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1923_ = lean_unbox_usize(v_i_1920_);
    lean_dec(v_i_1920_);
    v_stop_boxed_1924_ = lean_unbox_usize(v_stop_1921_);
    lean_dec(v_stop_1921_);
    v_res_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1915_, v_00_u03b2_1916_, v_00_u03c3_1917_, v_f_1918_, v_as_1919_, v_i_boxed_1923_, v_stop_boxed_1924_, v_b_1922_);
    lean_dec_ref(v_as_1919_);
    return v_res_1925_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03c3_1926_: *mut LeanObject,
    mut v_00_u03b1_1927_: *mut LeanObject,
    mut v_00_u03b2_1928_: *mut LeanObject,
    mut v_f_1929_: *mut LeanObject,
    mut v_keys_1930_: *mut LeanObject,
    mut v_vals_1931_: *mut LeanObject,
    mut v_heq_1932_: *mut LeanObject,
    mut v_i_1933_: *mut LeanObject,
    mut v_acc_1934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    v___x_1935_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_1929_, v_keys_1930_, v_vals_1931_, v_i_1933_, v_acc_1934_);
    return v___x_1935_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03c3_1936_: *mut LeanObject,
    mut v_00_u03b1_1937_: *mut LeanObject,
    mut v_00_u03b2_1938_: *mut LeanObject,
    mut v_f_1939_: *mut LeanObject,
    mut v_keys_1940_: *mut LeanObject,
    mut v_vals_1941_: *mut LeanObject,
    mut v_heq_1942_: *mut LeanObject,
    mut v_i_1943_: *mut LeanObject,
    mut v_acc_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1945_: *mut LeanObject = core::ptr::null_mut();
    v_res_1945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_1936_, v_00_u03b1_1937_, v_00_u03b2_1938_, v_f_1939_, v_keys_1940_, v_vals_1941_, v_heq_1942_, v_i_1943_, v_acc_1944_);
    lean_dec_ref(v_vals_1941_);
    lean_dec_ref(v_keys_1940_);
    return v_res_1945_;
}
pub unsafe fn l_Lean_collectAxioms___redArg___lam__0(
    mut v___x_1946_: *mut LeanObject,
    mut v_constName_1947_: *mut LeanObject,
    mut v_toPure_1948_: *mut LeanObject,
    mut v_env_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1950_: u8 = 0;
    let mut v_privateEnv_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    v___x_1950_ = 0;
    lean_inc_ref(v_env_1949_);
    v_privateEnv_1951_ = l_Lean_Environment_setExporting(v_env_1949_, v___x_1950_);
    v___x_1952_ = l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt;
    v___x_1953_ = lean_box(2);
    v___x_1954_ = lean_box(0);
    v_s_1955_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_1946_,
        v___x_1952_,
        v_env_1949_,
        v___x_1953_,
        v___x_1954_,
    );
    v___x_1956_ = lean_alloc_closure(
        l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_1956_, 0, v_s_1955_);
    v___x_1957_ = lean_alloc_closure(
        l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_1957_, 0, v___x_1956_);
    lean_closure_set(v___x_1957_, 1, v_constName_1947_);
    v___x_1958_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
        v_privateEnv_1951_,
        v___x_1957_,
    );
    v___x_1959_ = lean_apply_2(v_toPure_1948_, lean_box(0), v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn l_Lean_collectAxioms___redArg(
    mut v_inst_1960_: *mut LeanObject,
    mut v_inst_1961_: *mut LeanObject,
    mut v_constName_1962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1963_ = lean_ctor_get(v_inst_1960_, 0);
    lean_inc_ref(v_toApplicative_1963_);
    v_toBind_1964_ = lean_ctor_get(v_inst_1960_, 1);
    lean_inc(v_toBind_1964_);
    lean_dec_ref(v_inst_1960_);
    v_getEnv_1965_ = lean_ctor_get(v_inst_1961_, 0);
    lean_inc(v_getEnv_1965_);
    lean_dec_ref(v_inst_1961_);
    v_toPure_1966_ = lean_ctor_get(v_toApplicative_1963_, 1);
    lean_inc(v_toPure_1966_);
    lean_dec_ref(v_toApplicative_1963_);
    v___x_1967_ = l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState;
    v___f_1968_ = lean_alloc_closure(
        l_Lean_collectAxioms___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1968_, 0, v___x_1967_);
    lean_closure_set(v___f_1968_, 1, v_constName_1962_);
    lean_closure_set(v___f_1968_, 2, v_toPure_1966_);
    v___x_1969_ = lean_apply_4(
        v_toBind_1964_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1965_,
        v___f_1968_,
    );
    return v___x_1969_;
}
pub unsafe fn l_Lean_collectAxioms(
    mut v_m_1970_: *mut LeanObject,
    mut v_inst_1971_: *mut LeanObject,
    mut v_inst_1972_: *mut LeanObject,
    mut v_constName_1973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    v___x_1974_ = l_Lean_collectAxioms___redArg(v_inst_1971_, v_inst_1972_, v_constName_1973_);
    return v___x_1974_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_CollectAxioms(builtin: u8) -> *mut LeanObject {
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
    res = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt = lean_io_result_get_value(res);
    lean_mark_persistent(l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_CollectAxioms(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_CollectAxioms(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Util_CollectAxioms(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_CollectAxioms(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_CollectAxioms(builtin);
}
