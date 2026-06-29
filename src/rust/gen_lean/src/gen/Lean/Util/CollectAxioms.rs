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
use crate::ffi::lean_task_get_own;
use crate::ffi::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::ffi::lean_nat_shiftr;
use crate::ffi::lean_string_append;
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0_value:
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
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 46, 99, 111, 108, 108, 101, 99, 116, 65, 110, 100, 71, 101, 116, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 111, 108, 108, 101, 99, 116, 65, 110, 100, 71, 101, 116, 58, 32, 39, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [39, 32, 110, 111, 116, 32, 105, 110, 32, 115, 101, 101, 110, 32, 97, 102, 116, 101, 114, 32, 99, 111, 108, 108, 101, 99, 116, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + core::mem::size_of::<usize>()*1) as u16, other: 1, tag: 0 }, m_objs: [(0 as *mut crate::leanh::LeanObject)] };
pub static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 116, 105, 108, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11246366368068211756 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16007987903351044003 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,4211746031378004846 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14374199986448060823 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 120, 112, 111, 114, 116, 101, 100, 65, 120, 105, 111, 109, 115, 69, 120, 116, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14140705196984542656 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<8> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = l_Lean_NameSet_empty;
    v___x_989_ = crate::leanh::lean_box(1);
    v___x_990_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_990_, 0, v___x_989_);
    crate::leanh::lean_ctor_set(v___x_990_, 1, v___x_988_);
    return v___x_990_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
    mut v_env_991_: *mut crate::leanh::LeanObject,
    mut v_x_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0_once), _init_l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0);
    v___x_994_ = crate::leanh::lean_apply_2(v_x_992_, v_env_991_, v___x_993_);
    v_fst_995_ = crate::leanh::lean_ctor_get(v___x_994_, 0);
    crate::leanh::lean_inc(v_fst_995_);
    crate::leanh::lean_dec_ref(v___x_994_);
    return v_fst_995_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM(
    mut v_00_u03b1_996_: *mut crate::leanh::LeanObject,
    mut v_env_997_: *mut crate::leanh::LeanObject,
    mut v_x_998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
        v_env_997_, v_x_998_,
    );
    return v___x_999_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(
    mut v_as_1000_: *mut crate::leanh::LeanObject,
    mut v_i_1001_: usize,
    mut v_stop_1002_: usize,
    mut v_b_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: usize = 0;
    let mut v___x_1008_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1004_ = lean_usize_dec_eq(v_i_1001_, v_stop_1002_);
                if v___x_1004_ == 0 {
                    v___x_1005_ = lean_array_uget_borrowed(v_as_1000_, v_i_1001_);
                    crate::leanh::lean_inc(v___x_1005_);
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
    mut v_as_1010_: *mut crate::leanh::LeanObject,
    mut v_i_1011_: *mut crate::leanh::LeanObject,
    mut v_stop_1012_: *mut crate::leanh::LeanObject,
    mut v_b_1013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1014_: usize = 0;
    let mut v_stop_boxed_1015_: usize = 0;
    let mut v_res_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1014_ = crate::leanh::lean_unbox_usize(v_i_1011_);
    crate::leanh::lean_dec(v_i_1011_);
    v_stop_boxed_1015_ = crate::leanh::lean_unbox_usize(v_stop_1012_);
    crate::leanh::lean_dec(v_stop_1012_);
    v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_as_1010_, v_i_boxed_1014_, v_stop_boxed_1015_, v_b_1013_);
    crate::leanh::lean_dec_ref(v_as_1010_);
    return v_res_1016_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
    mut v_s_1017_: *mut crate::leanh::LeanObject,
    mut v_axs_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: u8 = 0;
    v___x_1019_ = crate::leanh::lean_unsigned_to_nat(0);
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
                let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1023_ = 0usize;
                v___x_1024_ = lean_usize_of_nat(v___x_1020_);
                v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_axs_1018_, v___x_1023_, v___x_1024_, v_s_1017_);
                return v___x_1025_;
            }
        } else {
            let mut v___x_1026_: usize = 0;
            let mut v___x_1027_: usize = 0;
            let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1026_ = 0usize;
            v___x_1027_ = lean_usize_of_nat(v___x_1020_);
            v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_axs_1018_, v___x_1026_, v___x_1027_, v_s_1017_);
            return v___x_1028_;
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray___boxed(
    mut v_s_1029_: *mut crate::leanh::LeanObject,
    mut v_axs_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
        v_s_1029_,
        v_axs_1030_,
    );
    crate::leanh::lean_dec_ref(v_axs_1030_);
    return v_res_1031_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(
    mut v_init_1032_: *mut crate::leanh::LeanObject,
    mut v_x_1033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1033_) == 0 {
                    v_k_1034_ = crate::leanh::lean_ctor_get(v_x_1033_, 1);
                    crate::leanh::lean_inc(v_k_1034_);
                    v_l_1035_ = crate::leanh::lean_ctor_get(v_x_1033_, 3);
                    crate::leanh::lean_inc(v_l_1035_);
                    v_r_1036_ = crate::leanh::lean_ctor_get(v_x_1033_, 4);
                    crate::leanh::lean_inc(v_r_1036_);
                    crate::leanh::lean_dec_ref_known(v_x_1033_, 5);
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
    mut v_hi_1040_: *mut crate::leanh::LeanObject,
    mut v_pivot_1041_: *mut crate::leanh::LeanObject,
    mut v_as_1042_: *mut crate::leanh::LeanObject,
    mut v_i_1043_: *mut crate::leanh::LeanObject,
    mut v_k_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1045_: u8 = 0;
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: u8 = 0;
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1045_ = lean_nat_dec_lt(v_k_1044_, v_hi_1040_);
                if v___x_1045_ == 0 {
                    crate::leanh::lean_dec(v_k_1044_);
                    v___x_1046_ = lean_array_fswap(v_as_1042_, v_i_1043_, v_hi_1040_);
                    v___x_1047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1047_, 0, v_i_1043_);
                    crate::leanh::lean_ctor_set(v___x_1047_, 1, v___x_1046_);
                    return v___x_1047_;
                } else {
                    v___x_1048_ = lean_array_fget_borrowed(v_as_1042_, v_k_1044_);
                    v___x_1049_ = l_Lean_Name_lt(v___x_1048_, v_pivot_1041_);
                    if v___x_1049_ == 0 {
                        v___x_1050_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1051_ = lean_nat_add(v_k_1044_, v___x_1050_);
                        crate::leanh::lean_dec(v_k_1044_);
                        v_k_1044_ = v___x_1051_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1053_ = lean_array_fswap(v_as_1042_, v_i_1043_, v_k_1044_);
                        v___x_1054_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1055_ = lean_nat_add(v_i_1043_, v___x_1054_);
                        crate::leanh::lean_dec(v_i_1043_);
                        v___x_1056_ = lean_nat_add(v_k_1044_, v___x_1054_);
                        crate::leanh::lean_dec(v_k_1044_);
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
    mut v_hi_1058_: *mut crate::leanh::LeanObject,
    mut v_pivot_1059_: *mut crate::leanh::LeanObject,
    mut v_as_1060_: *mut crate::leanh::LeanObject,
    mut v_i_1061_: *mut crate::leanh::LeanObject,
    mut v_k_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_1058_, v_pivot_1059_, v_as_1060_, v_i_1061_, v_k_1062_);
    crate::leanh::lean_dec(v_pivot_1059_);
    crate::leanh::lean_dec(v_hi_1058_);
    return v_res_1063_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(
    mut v_n_1064_: *mut crate::leanh::LeanObject,
    mut v_as_1065_: *mut crate::leanh::LeanObject,
    mut v_lo_1066_: *mut crate::leanh::LeanObject,
    mut v_hi_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: u8 = 0;
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: u8 = 0;
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1079_ = lean_nat_dec_lt(v_lo_1066_, v_hi_1067_);
                if v___x_1079_ == 0 {
                    crate::leanh::lean_dec(v_lo_1066_);
                    return v_as_1065_;
                } else {
                    v___x_1080_ = lean_nat_add(v_lo_1066_, v_hi_1067_);
                    v___x_1081_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_1082_ = lean_nat_shiftr(v___x_1080_, v___x_1081_);
                    crate::leanh::lean_dec(v___x_1080_);
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
                crate::leanh::lean_inc_n(v_lo_1066_, 2);
                v___x_1071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_1067_, v_pivot_1070_, v___y_1069_, v_lo_1066_, v_lo_1066_);
                crate::leanh::lean_dec(v_pivot_1070_);
                v_fst_1072_ = crate::leanh::lean_ctor_get(v___x_1071_, 0);
                crate::leanh::lean_inc(v_fst_1072_);
                v_snd_1073_ = crate::leanh::lean_ctor_get(v___x_1071_, 1);
                crate::leanh::lean_inc(v_snd_1073_);
                crate::leanh::lean_dec_ref(v___x_1071_);
                v___x_1074_ = lean_nat_dec_le(v_hi_1067_, v_fst_1072_);
                if v___x_1074_ == 0 {
                    v___x_1075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_1064_, v_snd_1073_, v_lo_1066_, v_fst_1072_);
                    v___x_1076_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1077_ = lean_nat_add(v_fst_1072_, v___x_1076_);
                    crate::leanh::lean_dec(v_fst_1072_);
                    v_as_1065_ = v___x_1075_;
                    v_lo_1066_ = v___x_1077_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1072_);
                    crate::leanh::lean_dec(v_lo_1066_);
                    return v_snd_1073_;
                }
            }
            2 => {
                v___x_1085_ = lean_array_fget_borrowed(v___y_1084_, v_mid_1082_);
                v___x_1086_ = lean_array_fget_borrowed(v___y_1084_, v_hi_1067_);
                v___x_1087_ = l_Lean_Name_lt(v___x_1085_, v___x_1086_);
                if v___x_1087_ == 0 {
                    crate::leanh::lean_dec(v_mid_1082_);
                    v___y_1069_ = v___y_1084_;
                    state = 1;
                    continue;
                } else {
                    v___x_1088_ = lean_array_fswap(v___y_1084_, v_mid_1082_, v_hi_1067_);
                    crate::leanh::lean_dec(v_mid_1082_);
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
    mut v_n_1099_: *mut crate::leanh::LeanObject,
    mut v_as_1100_: *mut crate::leanh::LeanObject,
    mut v_lo_1101_: *mut crate::leanh::LeanObject,
    mut v_hi_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1103_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_1099_, v_as_1100_, v_lo_1101_, v_hi_1102_);
    crate::leanh::lean_dec(v_hi_1102_);
    crate::leanh::lean_dec(v_n_1099_);
    return v_res_1103_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(
    mut v_extFind_x3f_1106_: *mut crate::leanh::LeanObject,
    mut v_as_1107_: *mut crate::leanh::LeanObject,
    mut v_i_1108_: usize,
    mut v_stop_1109_: usize,
    mut v_b_1110_: *mut crate::leanh::LeanObject,
    mut v___y_1111_: *mut crate::leanh::LeanObject,
    mut v___y_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1113_: u8 = 0;
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: usize = 0;
    let mut v___x_1119_: usize = 0;
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1113_ = lean_usize_dec_eq(v_i_1108_, v_stop_1109_);
                if v___x_1113_ == 0 {
                    v___x_1114_ = lean_array_uget_borrowed(v_as_1107_, v_i_1108_);
                    crate::leanh::lean_inc(v___x_1114_);
                    crate::leanh::lean_inc_ref(v_extFind_x3f_1106_);
                    v___x_1115_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
                        v_extFind_x3f_1106_,
                        v___x_1114_,
                        v___y_1111_,
                        v___y_1112_,
                    );
                    v_fst_1116_ = crate::leanh::lean_ctor_get(v___x_1115_, 0);
                    crate::leanh::lean_inc(v_fst_1116_);
                    v_snd_1117_ = crate::leanh::lean_ctor_get(v___x_1115_, 1);
                    crate::leanh::lean_inc(v_snd_1117_);
                    crate::leanh::lean_dec_ref(v___x_1115_);
                    v___x_1118_ = 1usize;
                    v___x_1119_ = lean_usize_add(v_i_1108_, v___x_1118_);
                    v_i_1108_ = v___x_1119_;
                    v_b_1110_ = v_fst_1116_;
                    v___y_1112_ = v_snd_1117_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_extFind_x3f_1106_);
                    v___x_1121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1121_, 0, v_b_1110_);
                    crate::leanh::lean_ctor_set(v___x_1121_, 1, v___y_1112_);
                    return v___x_1121_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(
    mut v_extFind_x3f_1122_: *mut crate::leanh::LeanObject,
    mut v_e_1123_: *mut crate::leanh::LeanObject,
    mut v___y_1124_: *mut crate::leanh::LeanObject,
    mut v___y_1125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: u8 = 0;
    v___x_1126_ = l_Lean_Expr_getUsedConstants(v_e_1123_);
    v___x_1127_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1128_ = lean_array_get_size(v___x_1126_);
    v___x_1129_ = crate::leanh::lean_box(0);
    v___x_1130_ = lean_nat_dec_lt(v___x_1127_, v___x_1128_);
    if v___x_1130_ == 0 {
        let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1126_);
        crate::leanh::lean_dec_ref(v_extFind_x3f_1122_);
        v___x_1131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1131_, 0, v___x_1129_);
        crate::leanh::lean_ctor_set(v___x_1131_, 1, v___y_1125_);
        return v___x_1131_;
    } else {
        let mut v___x_1132_: u8 = 0;
        v___x_1132_ = lean_nat_dec_le(v___x_1128_, v___x_1128_);
        if v___x_1132_ == 0 {
            if v___x_1130_ == 0 {
                let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_1126_);
                crate::leanh::lean_dec_ref(v_extFind_x3f_1122_);
                v___x_1133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1133_, 0, v___x_1129_);
                crate::leanh::lean_ctor_set(v___x_1133_, 1, v___y_1125_);
                return v___x_1133_;
            } else {
                let mut v___x_1134_: usize = 0;
                let mut v___x_1135_: usize = 0;
                let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1134_ = 0usize;
                v___x_1135_ = lean_usize_of_nat(v___x_1128_);
                v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_1122_, v___x_1126_, v___x_1134_, v___x_1135_, v___x_1129_, v___y_1124_, v___y_1125_);
                crate::leanh::lean_dec_ref(v___x_1126_);
                return v___x_1136_;
            }
        } else {
            let mut v___x_1137_: usize = 0;
            let mut v___x_1138_: usize = 0;
            let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1137_ = 0usize;
            v___x_1138_ = lean_usize_of_nat(v___x_1128_);
            v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_1122_, v___x_1126_, v___x_1137_, v___x_1138_, v___x_1129_, v___y_1124_, v___y_1125_);
            crate::leanh::lean_dec_ref(v___x_1126_);
            return v___x_1139_;
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
    mut v_extFind_x3f_1140_: *mut crate::leanh::LeanObject,
    mut v_c_1141_: *mut crate::leanh::LeanObject,
    mut v_a_1142_: *mut crate::leanh::LeanObject,
    mut v_a_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_axioms_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1158_: u8 = 0;
    let mut v_seen_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_axioms_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___y_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1170_: u8 = 0;
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v_unused_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: u8 = 0;
    let mut v___y_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___y_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_axioms_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_axioms_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_extFind_x3f_1140_);
                crate::leanh::lean_inc(v_c_1141_);
                crate::leanh::lean_inc_ref(v_a_1142_);
                v___x_1144_ = crate::leanh::lean_apply_2(v_extFind_x3f_1140_, v_a_1142_, v_c_1141_);
                if crate::leanh::lean_obj_tag(v___x_1144_) == 1 {
                    crate::leanh::lean_dec_ref(v_extFind_x3f_1140_);
                    v_val_1145_ = crate::leanh::lean_ctor_get(v___x_1144_, 0);
                    crate::leanh::lean_inc(v_val_1145_);
                    crate::leanh::lean_dec_ref_known(v___x_1144_, 1);
                    v_seen_1146_ = crate::leanh::lean_ctor_get(v_a_1143_, 0);
                    v_axioms_1147_ = crate::leanh::lean_ctor_get(v_a_1143_, 1);
                    v_isSharedCheck_1158_ = (!crate::leanh::lean_is_exclusive(v_a_1143_)) as u8;
                    if v_isSharedCheck_1158_ == 0 {
                        v___x_1149_ = v_a_1143_;
                        v_isShared_1150_ = v_isSharedCheck_1158_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_axioms_1147_);
                        crate::leanh::lean_inc(v_seen_1146_);
                        crate::leanh::lean_dec(v_a_1143_);
                        v___x_1149_ = crate::leanh::lean_box(0);
                        v_isShared_1150_ = v_isSharedCheck_1158_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1144_);
                    v_seen_1159_ = crate::leanh::lean_ctor_get(v_a_1143_, 0);
                    v_axioms_1160_ = crate::leanh::lean_ctor_get(v_a_1143_, 1);
                    v_isSharedCheck_1265_ = (!crate::leanh::lean_is_exclusive(v_a_1143_)) as u8;
                    if v_isSharedCheck_1265_ == 0 {
                        v___x_1162_ = v_a_1143_;
                        v_isShared_1163_ = v_isSharedCheck_1265_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_axioms_1160_);
                        crate::leanh::lean_inc(v_seen_1159_);
                        crate::leanh::lean_dec(v_a_1143_);
                        v___x_1162_ = crate::leanh::lean_box(0);
                        v_isShared_1163_ = v_isSharedCheck_1265_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_val_1145_);
                v___x_1151_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_1141_, v_val_1145_, v_seen_1146_);
                v___x_1152_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
                    v_axioms_1147_,
                    v_val_1145_,
                );
                crate::leanh::lean_dec(v_val_1145_);
                if v_isShared_1150_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1149_, 1, v___x_1152_);
                    crate::leanh::lean_ctor_set(v___x_1149_, 0, v___x_1151_);
                    v___x_1154_ = v___x_1149_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1157_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1151_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1152_);
                    v___x_1154_ = v_reuseFailAlloc_1157_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1155_ = crate::leanh::lean_box(0);
                v___x_1156_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1155_);
                crate::leanh::lean_ctor_set(v___x_1156_, 1, v___x_1154_);
                return v___x_1156_;
            }
            3 => {
                v___x_1214_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_seen_1159_, v_c_1141_);
                if crate::leanh::lean_obj_tag(v___x_1214_) == 1 {
                    crate::leanh::lean_dec(v_c_1141_);
                    crate::leanh::lean_dec_ref(v_extFind_x3f_1140_);
                    v_val_1215_ = crate::leanh::lean_ctor_get(v___x_1214_, 0);
                    crate::leanh::lean_inc(v_val_1215_);
                    crate::leanh::lean_dec_ref_known(v___x_1214_, 1);
                    v___x_1216_ =
                        l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
                            v_axioms_1160_,
                            v_val_1215_,
                        );
                    crate::leanh::lean_dec(v_val_1215_);
                    if v_isShared_1163_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1162_, 1, v___x_1216_);
                        v___x_1218_ = v___x_1162_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1221_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_seen_1159_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1216_);
                        v___x_1218_ = v_reuseFailAlloc_1221_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1214_);
                    v_checked_1222_ = crate::leanh::lean_ctor_get(v_a_1142_, 2);
                    v___x_1223_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0;
                    crate::leanh::lean_inc(v_c_1141_);
                    v___x_1224_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_1141_, v___x_1223_, v_seen_1159_);
                    v___x_1225_ = l_Lean_NameSet_empty;
                    crate::leanh::lean_inc(v___x_1224_);
                    if v_isShared_1163_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1162_, 1, v___x_1225_);
                        crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1224_);
                        v___x_1227_ = v___x_1162_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1264_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1224_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1225_);
                        v___x_1227_ = v_reuseFailAlloc_1264_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_seen_1167_ = crate::leanh::lean_ctor_get(v___y_1165_, 0);
                v_isSharedCheck_1178_ = (!crate::leanh::lean_is_exclusive(v___y_1165_)) as u8;
                if v_isSharedCheck_1178_ == 0 {
                    v_unused_1179_ = crate::leanh::lean_ctor_get(v___y_1165_, 1);
                    crate::leanh::lean_dec(v_unused_1179_);
                    v___x_1169_ = v___y_1165_;
                    v_isShared_1170_ = v_isSharedCheck_1178_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_seen_1167_);
                    crate::leanh::lean_dec(v___y_1165_);
                    v___x_1169_ = crate::leanh::lean_box(0);
                    v_isShared_1170_ = v_isSharedCheck_1178_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1171_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc_ref(v___y_1166_);
                v___x_1172_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_1141_, v___y_1166_, v_seen_1167_);
                v___x_1173_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
                    v_axioms_1160_,
                    v___y_1166_,
                );
                crate::leanh::lean_dec_ref(v___y_1166_);
                if v_isShared_1170_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1169_, 1, v___x_1173_);
                    crate::leanh::lean_ctor_set(v___x_1169_, 0, v___x_1172_);
                    v___x_1175_ = v___x_1169_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1173_);
                    v___x_1175_ = v_reuseFailAlloc_1177_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1176_, 0, v___x_1171_);
                crate::leanh::lean_ctor_set(v___x_1176_, 1, v___x_1175_);
                return v___x_1176_;
            }
            7 => {
                v___x_1186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v___y_1181_, v___y_1183_, v___y_1182_, v___y_1185_);
                crate::leanh::lean_dec(v___y_1185_);
                crate::leanh::lean_dec(v___y_1181_);
                v___y_1165_ = v___y_1184_;
                v___y_1166_ = v___x_1186_;
                state = 4;
                continue;
            }
            8 => {
                v___x_1193_ = lean_nat_dec_le(v___y_1192_, v___y_1189_);
                if v___x_1193_ == 0 {
                    crate::leanh::lean_dec(v___y_1189_);
                    crate::leanh::lean_inc(v___y_1192_);
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
                crate::leanh::lean_dec(v___y_1197_);
                v___x_1199_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v___x_1198_, v___y_1195_);
                v___x_1200_ = lean_array_get_size(v___x_1199_);
                v___x_1201_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1202_ = lean_nat_dec_eq(v___x_1200_, v___x_1201_);
                if v___x_1202_ == 0 {
                    v___x_1203_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1204_ = lean_nat_sub(v___x_1200_, v___x_1203_);
                    v___x_1205_ = lean_nat_dec_le(v___x_1201_, v___x_1204_);
                    if v___x_1205_ == 0 {
                        crate::leanh::lean_inc(v___x_1204_);
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
                if crate::leanh::lean_obj_tag(v_axioms_1208_) == 0 {
                    v_size_1209_ = crate::leanh::lean_ctor_get(v_axioms_1208_, 0);
                    crate::leanh::lean_inc(v_size_1209_);
                    v___y_1195_ = v_axioms_1208_;
                    v___y_1196_ = v___y_1207_;
                    v___y_1197_ = v_size_1209_;
                    state = 9;
                    continue;
                } else {
                    v___x_1210_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1195_ = v_axioms_1208_;
                    v___y_1196_ = v___y_1207_;
                    v___y_1197_ = v___x_1210_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_axioms_1213_ = crate::leanh::lean_ctor_get(v___y_1212_, 1);
                crate::leanh::lean_inc(v_axioms_1213_);
                v___y_1207_ = v___y_1212_;
                v_axioms_1208_ = v_axioms_1213_;
                state = 10;
                continue;
            }
            12 => {
                v___x_1219_ = crate::leanh::lean_box(0);
                v___x_1220_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1220_, 0, v___x_1219_);
                crate::leanh::lean_ctor_set(v___x_1220_, 1, v___x_1218_);
                return v___x_1220_;
            }
            13 => {
                crate::leanh::lean_inc_ref(v_checked_1222_);
                v___x_1228_ = lean_task_get_own(v_checked_1222_);
                crate::leanh::lean_inc(v_c_1141_);
                v___x_1229_ = lean_environment_find(v___x_1228_, v_c_1141_);
                if crate::leanh::lean_obj_tag(v___x_1229_) == 0 {
                    crate::leanh::lean_dec(v___x_1224_);
                    crate::leanh::lean_dec_ref(v_extFind_x3f_1140_);
                    v___y_1207_ = v___x_1227_;
                    v_axioms_1208_ = v___x_1225_;
                    state = 10;
                    continue;
                } else {
                    v_val_1230_ = crate::leanh::lean_ctor_get(v___x_1229_, 0);
                    crate::leanh::lean_inc(v_val_1230_);
                    crate::leanh::lean_dec_ref_known(v___x_1229_, 1);
                    match crate::leanh::lean_obj_tag(v_val_1230_) {
                        0 => {
                            crate::leanh::lean_dec_ref(v___x_1227_);
                            v_val_1231_ = crate::leanh::lean_ctor_get(v_val_1230_, 0);
                            crate::leanh::lean_inc_ref(v_val_1231_);
                            crate::leanh::lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1232_ = crate::leanh::lean_ctor_get(v_val_1231_, 0);
                            crate::leanh::lean_inc_ref(v_toConstantVal_1232_);
                            crate::leanh::lean_dec_ref(v_val_1231_);
                            v_type_1233_ = crate::leanh::lean_ctor_get(v_toConstantVal_1232_, 2);
                            crate::leanh::lean_inc_ref(v_type_1233_);
                            crate::leanh::lean_dec_ref(v_toConstantVal_1232_);
                            crate::leanh::lean_inc(v_c_1141_);
                            v___x_1234_ = l_Lean_NameSet_insert(v___x_1225_, v_c_1141_);
                            v___x_1235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1235_, 0, v___x_1224_);
                            crate::leanh::lean_ctor_set(v___x_1235_, 1, v___x_1234_);
                            v___x_1236_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1233_, v_a_1142_, v___x_1235_);
                            v_snd_1237_ = crate::leanh::lean_ctor_get(v___x_1236_, 1);
                            crate::leanh::lean_inc(v_snd_1237_);
                            crate::leanh::lean_dec_ref(v___x_1236_);
                            v___y_1212_ = v_snd_1237_;
                            state = 11;
                            continue;
                        }
                        4 => {
                            crate::leanh::lean_dec_ref_known(v_val_1230_, 1);
                            crate::leanh::lean_dec(v___x_1224_);
                            crate::leanh::lean_dec_ref(v_extFind_x3f_1140_);
                            v___y_1207_ = v___x_1227_;
                            v_axioms_1208_ = v___x_1225_;
                            state = 10;
                            continue;
                        }
                        5 => {
                            crate::leanh::lean_dec(v___x_1224_);
                            v_val_1238_ = crate::leanh::lean_ctor_get(v_val_1230_, 0);
                            crate::leanh::lean_inc_ref(v_val_1238_);
                            crate::leanh::lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1239_ = crate::leanh::lean_ctor_get(v_val_1238_, 0);
                            crate::leanh::lean_inc_ref(v_toConstantVal_1239_);
                            v_ctors_1240_ = crate::leanh::lean_ctor_get(v_val_1238_, 4);
                            crate::leanh::lean_inc(v_ctors_1240_);
                            crate::leanh::lean_dec_ref(v_val_1238_);
                            v_type_1241_ = crate::leanh::lean_ctor_get(v_toConstantVal_1239_, 2);
                            crate::leanh::lean_inc_ref(v_type_1241_);
                            crate::leanh::lean_dec_ref(v_toConstantVal_1239_);
                            crate::leanh::lean_inc_ref(v_extFind_x3f_1140_);
                            v___x_1242_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1241_, v_a_1142_, v___x_1227_);
                            v_snd_1243_ = crate::leanh::lean_ctor_get(v___x_1242_, 1);
                            crate::leanh::lean_inc(v_snd_1243_);
                            crate::leanh::lean_dec_ref(v___x_1242_);
                            v___x_1244_ = l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(v_extFind_x3f_1140_, v_ctors_1240_, v_a_1142_, v_snd_1243_);
                            v_snd_1245_ = crate::leanh::lean_ctor_get(v___x_1244_, 1);
                            crate::leanh::lean_inc(v_snd_1245_);
                            crate::leanh::lean_dec_ref(v___x_1244_);
                            v___y_1212_ = v_snd_1245_;
                            state = 11;
                            continue;
                        }
                        6 => {
                            crate::leanh::lean_dec(v___x_1224_);
                            v_val_1246_ = crate::leanh::lean_ctor_get(v_val_1230_, 0);
                            crate::leanh::lean_inc_ref(v_val_1246_);
                            crate::leanh::lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1247_ = crate::leanh::lean_ctor_get(v_val_1246_, 0);
                            crate::leanh::lean_inc_ref(v_toConstantVal_1247_);
                            crate::leanh::lean_dec_ref(v_val_1246_);
                            v_type_1248_ = crate::leanh::lean_ctor_get(v_toConstantVal_1247_, 2);
                            crate::leanh::lean_inc_ref(v_type_1248_);
                            crate::leanh::lean_dec_ref(v_toConstantVal_1247_);
                            v___x_1249_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1248_, v_a_1142_, v___x_1227_);
                            v_snd_1250_ = crate::leanh::lean_ctor_get(v___x_1249_, 1);
                            crate::leanh::lean_inc(v_snd_1250_);
                            crate::leanh::lean_dec_ref(v___x_1249_);
                            v___y_1212_ = v_snd_1250_;
                            state = 11;
                            continue;
                        }
                        7 => {
                            crate::leanh::lean_dec(v___x_1224_);
                            v_val_1251_ = crate::leanh::lean_ctor_get(v_val_1230_, 0);
                            crate::leanh::lean_inc_ref(v_val_1251_);
                            crate::leanh::lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1252_ = crate::leanh::lean_ctor_get(v_val_1251_, 0);
                            crate::leanh::lean_inc_ref(v_toConstantVal_1252_);
                            crate::leanh::lean_dec_ref(v_val_1251_);
                            v_type_1253_ = crate::leanh::lean_ctor_get(v_toConstantVal_1252_, 2);
                            crate::leanh::lean_inc_ref(v_type_1253_);
                            crate::leanh::lean_dec_ref(v_toConstantVal_1252_);
                            v___x_1254_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1253_, v_a_1142_, v___x_1227_);
                            v_snd_1255_ = crate::leanh::lean_ctor_get(v___x_1254_, 1);
                            crate::leanh::lean_inc(v_snd_1255_);
                            crate::leanh::lean_dec_ref(v___x_1254_);
                            v___y_1212_ = v_snd_1255_;
                            state = 11;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v___x_1224_);
                            v_val_1256_ = crate::leanh::lean_ctor_get(v_val_1230_, 0);
                            crate::leanh::lean_inc_ref(v_val_1256_);
                            crate::leanh::lean_dec(v_val_1230_);
                            v_toConstantVal_1257_ = crate::leanh::lean_ctor_get(v_val_1256_, 0);
                            crate::leanh::lean_inc_ref(v_toConstantVal_1257_);
                            v_value_1258_ = crate::leanh::lean_ctor_get(v_val_1256_, 1);
                            crate::leanh::lean_inc_ref(v_value_1258_);
                            crate::leanh::lean_dec_ref(v_val_1256_);
                            v_type_1259_ = crate::leanh::lean_ctor_get(v_toConstantVal_1257_, 2);
                            crate::leanh::lean_inc_ref(v_type_1259_);
                            crate::leanh::lean_dec_ref(v_toConstantVal_1257_);
                            crate::leanh::lean_inc_ref(v_extFind_x3f_1140_);
                            v___x_1260_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1259_, v_a_1142_, v___x_1227_);
                            v_snd_1261_ = crate::leanh::lean_ctor_get(v___x_1260_, 1);
                            crate::leanh::lean_inc(v_snd_1261_);
                            crate::leanh::lean_dec_ref(v___x_1260_);
                            v___x_1262_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_value_1258_, v_a_1142_, v_snd_1261_);
                            v_snd_1263_ = crate::leanh::lean_ctor_get(v___x_1262_, 1);
                            crate::leanh::lean_inc(v_snd_1263_);
                            crate::leanh::lean_dec_ref(v___x_1262_);
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
    mut v_extFind_x3f_1266_: *mut crate::leanh::LeanObject,
    mut v_as_1267_: *mut crate::leanh::LeanObject,
    mut v___y_1268_: *mut crate::leanh::LeanObject,
    mut v___y_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_1267_) == 0 {
                    crate::leanh::lean_dec_ref(v_extFind_x3f_1266_);
                    v___x_1270_ = crate::leanh::lean_box(0);
                    v___x_1271_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
                    crate::leanh::lean_ctor_set(v___x_1271_, 1, v___y_1269_);
                    return v___x_1271_;
                } else {
                    v_head_1272_ = crate::leanh::lean_ctor_get(v_as_1267_, 0);
                    crate::leanh::lean_inc(v_head_1272_);
                    v_tail_1273_ = crate::leanh::lean_ctor_get(v_as_1267_, 1);
                    crate::leanh::lean_inc(v_tail_1273_);
                    crate::leanh::lean_dec_ref_known(v_as_1267_, 2);
                    crate::leanh::lean_inc_ref(v_extFind_x3f_1266_);
                    v___x_1274_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
                        v_extFind_x3f_1266_,
                        v_head_1272_,
                        v___y_1268_,
                        v___y_1269_,
                    );
                    v_snd_1275_ = crate::leanh::lean_ctor_get(v___x_1274_, 1);
                    crate::leanh::lean_inc(v_snd_1275_);
                    crate::leanh::lean_dec_ref(v___x_1274_);
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
    mut v_extFind_x3f_1277_: *mut crate::leanh::LeanObject,
    mut v_as_1278_: *mut crate::leanh::LeanObject,
    mut v___y_1279_: *mut crate::leanh::LeanObject,
    mut v___y_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(v_extFind_x3f_1277_, v_as_1278_, v___y_1279_, v___y_1280_);
    crate::leanh::lean_dec_ref(v___y_1279_);
    return v_res_1281_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0___boxed(
    mut v_extFind_x3f_1282_: *mut crate::leanh::LeanObject,
    mut v_as_1283_: *mut crate::leanh::LeanObject,
    mut v_i_1284_: *mut crate::leanh::LeanObject,
    mut v_stop_1285_: *mut crate::leanh::LeanObject,
    mut v_b_1286_: *mut crate::leanh::LeanObject,
    mut v___y_1287_: *mut crate::leanh::LeanObject,
    mut v___y_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1289_: usize = 0;
    let mut v_stop_boxed_1290_: usize = 0;
    let mut v_res_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1289_ = crate::leanh::lean_unbox_usize(v_i_1284_);
    crate::leanh::lean_dec(v_i_1284_);
    v_stop_boxed_1290_ = crate::leanh::lean_unbox_usize(v_stop_1285_);
    crate::leanh::lean_dec(v_stop_1285_);
    v_res_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_1282_, v_as_1283_, v_i_boxed_1289_, v_stop_boxed_1290_, v_b_1286_, v___y_1287_, v___y_1288_);
    crate::leanh::lean_dec_ref(v___y_1287_);
    crate::leanh::lean_dec_ref(v_as_1283_);
    return v_res_1291_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0___boxed(
    mut v_extFind_x3f_1292_: *mut crate::leanh::LeanObject,
    mut v_e_1293_: *mut crate::leanh::LeanObject,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(
        v_extFind_x3f_1292_,
        v_e_1293_,
        v___y_1294_,
        v___y_1295_,
    );
    crate::leanh::lean_dec_ref(v___y_1294_);
    return v_res_1296_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___boxed(
    mut v_extFind_x3f_1297_: *mut crate::leanh::LeanObject,
    mut v_c_1298_: *mut crate::leanh::LeanObject,
    mut v_a_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
        v_extFind_x3f_1297_,
        v_c_1298_,
        v_a_1299_,
        v_a_1300_,
    );
    crate::leanh::lean_dec_ref(v_a_1299_);
    return v_res_1301_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1(
    mut v_init_1302_: *mut crate::leanh::LeanObject,
    mut v_t_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v_init_1302_, v_t_1303_);
    return v___x_1304_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(
    mut v_n_1305_: *mut crate::leanh::LeanObject,
    mut v_as_1306_: *mut crate::leanh::LeanObject,
    mut v_lo_1307_: *mut crate::leanh::LeanObject,
    mut v_hi_1308_: *mut crate::leanh::LeanObject,
    mut v_w_1309_: *mut crate::leanh::LeanObject,
    mut v_hlo_1310_: *mut crate::leanh::LeanObject,
    mut v_hhi_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_1305_, v_as_1306_, v_lo_1307_, v_hi_1308_);
    return v___x_1312_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___boxed(
    mut v_n_1313_: *mut crate::leanh::LeanObject,
    mut v_as_1314_: *mut crate::leanh::LeanObject,
    mut v_lo_1315_: *mut crate::leanh::LeanObject,
    mut v_hi_1316_: *mut crate::leanh::LeanObject,
    mut v_w_1317_: *mut crate::leanh::LeanObject,
    mut v_hlo_1318_: *mut crate::leanh::LeanObject,
    mut v_hhi_1319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(v_n_1313_, v_as_1314_, v_lo_1315_, v_hi_1316_, v_w_1317_, v_hlo_1318_, v_hhi_1319_);
    crate::leanh::lean_dec(v_hi_1316_);
    crate::leanh::lean_dec(v_n_1313_);
    return v_res_1320_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(
    mut v_n_1321_: *mut crate::leanh::LeanObject,
    mut v_lo_1322_: *mut crate::leanh::LeanObject,
    mut v_hi_1323_: *mut crate::leanh::LeanObject,
    mut v_hhi_1324_: *mut crate::leanh::LeanObject,
    mut v_pivot_1325_: *mut crate::leanh::LeanObject,
    mut v_as_1326_: *mut crate::leanh::LeanObject,
    mut v_i_1327_: *mut crate::leanh::LeanObject,
    mut v_k_1328_: *mut crate::leanh::LeanObject,
    mut v_ilo_1329_: *mut crate::leanh::LeanObject,
    mut v_ik_1330_: *mut crate::leanh::LeanObject,
    mut v_w_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_1323_, v_pivot_1325_, v_as_1326_, v_i_1327_, v_k_1328_);
    return v___x_1332_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___boxed(
    mut v_n_1333_: *mut crate::leanh::LeanObject,
    mut v_lo_1334_: *mut crate::leanh::LeanObject,
    mut v_hi_1335_: *mut crate::leanh::LeanObject,
    mut v_hhi_1336_: *mut crate::leanh::LeanObject,
    mut v_pivot_1337_: *mut crate::leanh::LeanObject,
    mut v_as_1338_: *mut crate::leanh::LeanObject,
    mut v_i_1339_: *mut crate::leanh::LeanObject,
    mut v_k_1340_: *mut crate::leanh::LeanObject,
    mut v_ilo_1341_: *mut crate::leanh::LeanObject,
    mut v_ik_1342_: *mut crate::leanh::LeanObject,
    mut v_w_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(v_n_1333_, v_lo_1334_, v_hi_1335_, v_hhi_1336_, v_pivot_1337_, v_as_1338_, v_i_1339_, v_k_1340_, v_ilo_1341_, v_ik_1342_, v_w_1343_);
    crate::leanh::lean_dec(v_pivot_1337_);
    crate::leanh::lean_dec(v_hi_1335_);
    crate::leanh::lean_dec(v_lo_1334_);
    crate::leanh::lean_dec(v_n_1333_);
    return v_res_1344_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1352_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_1352_;
}
pub unsafe fn l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(
    mut v_msg_1353_: *mut crate::leanh::LeanObject,
    mut v___y_1354_: *mut crate::leanh::LeanObject,
    mut v___y_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017__overap_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1356_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0;
    v___f_1357_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1;
    v___f_1358_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2;
    v___f_1359_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3;
    v___f_1360_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4;
    v___f_1361_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5;
    v___f_1362_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6;
    v___x_1363_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1363_, 0, v___f_1356_);
    crate::leanh::lean_ctor_set(v___x_1363_, 1, v___f_1357_);
    v___x_1364_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1364_, 0, v___x_1363_);
    crate::leanh::lean_ctor_set(v___x_1364_, 1, v___f_1358_);
    crate::leanh::lean_ctor_set(v___x_1364_, 2, v___f_1359_);
    crate::leanh::lean_ctor_set(v___x_1364_, 3, v___f_1360_);
    crate::leanh::lean_ctor_set(v___x_1364_, 4, v___f_1361_);
    v___x_1365_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1365_, 0, v___x_1364_);
    crate::leanh::lean_ctor_set(v___x_1365_, 1, v___f_1362_);
    crate::leanh::lean_inc_ref_n(v___x_1365_, 6);
    v___f_1366_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1366_, 0, v___x_1365_);
    v___f_1367_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1367_, 0, v___x_1365_);
    v___f_1368_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1368_, 0, v___x_1365_);
    v___f_1369_ = crate::leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1369_, 0, v___x_1365_);
    v___x_1370_ = crate::leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1370_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1370_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1370_, 2, v___x_1365_);
    v___x_1371_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1371_, 0, v___x_1370_);
    crate::leanh::lean_ctor_set(v___x_1371_, 1, v___f_1366_);
    v___x_1372_ = crate::leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    crate::leanh::lean_closure_set(v___x_1372_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1372_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1372_, 2, v___x_1365_);
    v___x_1373_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1373_, 0, v___x_1371_);
    crate::leanh::lean_ctor_set(v___x_1373_, 1, v___x_1372_);
    crate::leanh::lean_ctor_set(v___x_1373_, 2, v___f_1367_);
    crate::leanh::lean_ctor_set(v___x_1373_, 3, v___f_1368_);
    crate::leanh::lean_ctor_set(v___x_1373_, 4, v___f_1369_);
    v___x_1374_ = crate::leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___x_1374_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1374_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1374_, 2, v___x_1365_);
    v___x_1375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1375_, 0, v___x_1373_);
    crate::leanh::lean_ctor_set(v___x_1375_, 1, v___x_1374_);
    v___x_1376_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7_once), _init_l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7);
    v___x_1377_ = l_instInhabitedOfMonad___redArg(v___x_1375_, v___x_1376_);
    v___f_1378_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1378_, 0, v___x_1377_);
    v___x_1017__overap_1379_ = lean_panic_fn_borrowed(v___f_1378_, v_msg_1353_);
    crate::leanh::lean_dec_ref(v___f_1378_);
    crate::leanh::lean_inc_ref(v___y_1354_);
    v___x_1380_ = crate::leanh::lean_apply_2(v___x_1017__overap_1379_, v___y_1354_, v___y_1355_);
    return v___x_1380_;
}
pub unsafe fn l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___boxed(
    mut v_msg_1381_: *mut crate::leanh::LeanObject,
    mut v___y_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(v_msg_1381_, v___y_1382_, v___y_1383_);
    crate::leanh::lean_dec_ref(v___y_1382_);
    return v_res_1384_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(
    mut v_extFind_x3f_1389_: *mut crate::leanh::LeanObject,
    mut v_c_1390_: *mut crate::leanh::LeanObject,
    mut v_a_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1397_: u8 = 0;
    let mut v_seen_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: u8 = 0;
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1416_: u8 = 0;
    let mut v_unused_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_c_1390_);
                v___x_1393_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
                    v_extFind_x3f_1389_,
                    v_c_1390_,
                    v_a_1391_,
                    v_a_1392_,
                );
                v_snd_1394_ = crate::leanh::lean_ctor_get(v___x_1393_, 1);
                v_isSharedCheck_1416_ = (!crate::leanh::lean_is_exclusive(v___x_1393_)) as u8;
                if v_isSharedCheck_1416_ == 0 {
                    v_unused_1417_ = crate::leanh::lean_ctor_get(v___x_1393_, 0);
                    crate::leanh::lean_dec(v_unused_1417_);
                    v___x_1396_ = v___x_1393_;
                    v_isShared_1397_ = v_isSharedCheck_1416_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1394_);
                    crate::leanh::lean_dec(v___x_1393_);
                    v___x_1396_ = crate::leanh::lean_box(0);
                    v_isShared_1397_ = v_isSharedCheck_1416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_seen_1398_ = crate::leanh::lean_ctor_get(v_snd_1394_, 0);
                v___x_1399_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_seen_1398_, v_c_1390_);
                if crate::leanh::lean_obj_tag(v___x_1399_) == 1 {
                    crate::leanh::lean_dec(v_c_1390_);
                    v_val_1400_ = crate::leanh::lean_ctor_get(v___x_1399_, 0);
                    crate::leanh::lean_inc(v_val_1400_);
                    crate::leanh::lean_dec_ref_known(v___x_1399_, 1);
                    if v_isShared_1397_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1396_, 0, v_val_1400_);
                        v___x_1402_ = v___x_1396_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1403_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_val_1400_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_snd_1394_);
                        v___x_1402_ = v_reuseFailAlloc_1403_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1399_);
                    crate::leanh::lean_del_object(v___x_1396_);
                    v___x_1404_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0;
                    v___x_1405_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1;
                    v___x_1406_ = crate::leanh::lean_unsigned_to_nat(81);
                    v___x_1407_ = crate::leanh::lean_unsigned_to_nat(41);
                    v___x_1408_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2;
                    v___x_1409_ = 1;
                    v___x_1410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_c_1390_,
                        v___x_1409_,
                    );
                    v___x_1411_ = lean_string_append(v___x_1408_, v___x_1410_);
                    crate::leanh::lean_dec_ref(v___x_1410_);
                    v___x_1412_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3;
                    v___x_1413_ = lean_string_append(v___x_1411_, v___x_1412_);
                    v___x_1414_ = l_mkPanicMessageWithDecl(
                        v___x_1404_,
                        v___x_1405_,
                        v___x_1406_,
                        v___x_1407_,
                        v___x_1413_,
                    );
                    crate::leanh::lean_dec_ref(v___x_1413_);
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
    mut v_extFind_x3f_1418_: *mut crate::leanh::LeanObject,
    mut v_c_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1422_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(
        v_extFind_x3f_1418_,
        v_c_1419_,
        v_a_1420_,
        v_a_1421_,
    );
    crate::leanh::lean_dec_ref(v_a_1420_);
    return v_res_1422_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(
    mut v_a_1426_: *mut crate::leanh::LeanObject,
    mut v_b_1427_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: u8 = 0;
    v_fst_1428_ = crate::leanh::lean_ctor_get(v_a_1426_, 0);
    v_fst_1429_ = crate::leanh::lean_ctor_get(v_b_1427_, 0);
    v___x_1430_ = l_Lean_Name_quickLt(v_fst_1428_, v_fst_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0___boxed(
    mut v_a_1431_: *mut crate::leanh::LeanObject,
    mut v_b_1432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1433_: u8 = 0;
    let mut v_r_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1433_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_1431_, v_b_1432_);
    crate::leanh::lean_dec_ref(v_b_1432_);
    crate::leanh::lean_dec_ref(v_a_1431_);
    v_r_1434_ = crate::leanh::lean_box((v_res_1433_) as usize);
    return v_r_1434_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(
    mut v_as_1435_: *mut crate::leanh::LeanObject,
    mut v_k_1436_: *mut crate::leanh::LeanObject,
    mut v_x_1437_: *mut crate::leanh::LeanObject,
    mut v_x_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: u8 = 0;
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1439_ = lean_nat_add(v_x_1437_, v_x_1438_);
                v___x_1440_ = crate::leanh::lean_unsigned_to_nat(1);
                v_m_1441_ = lean_nat_shiftr(v___x_1439_, v___x_1440_);
                crate::leanh::lean_dec(v___x_1439_);
                v_a_1442_ = lean_array_fget_borrowed(v_as_1435_, v_m_1441_);
                v___x_1443_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_1442_, v_k_1436_);
                if v___x_1443_ == 0 {
                    crate::leanh::lean_dec(v_x_1438_);
                    v___x_1444_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_k_1436_, v_a_1442_);
                    if v___x_1444_ == 0 {
                        crate::leanh::lean_dec(v_m_1441_);
                        crate::leanh::lean_dec(v_x_1437_);
                        crate::leanh::lean_inc(v_a_1442_);
                        v___x_1445_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1445_, 0, v_a_1442_);
                        return v___x_1445_;
                    } else {
                        v___x_1446_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1447_ = lean_nat_dec_eq(v_m_1441_, v___x_1446_);
                        if v___x_1447_ == 0 {
                            v___x_1448_ = lean_nat_sub(v_m_1441_, v___x_1440_);
                            crate::leanh::lean_dec(v_m_1441_);
                            v___x_1449_ = lean_nat_dec_lt(v___x_1448_, v_x_1437_);
                            if v___x_1449_ == 0 {
                                v_x_1438_ = v___x_1448_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_1448_);
                                crate::leanh::lean_dec(v_x_1437_);
                                v___x_1451_ = crate::leanh::lean_box(0);
                                return v___x_1451_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_m_1441_);
                            crate::leanh::lean_dec(v_x_1437_);
                            v___x_1452_ = crate::leanh::lean_box(0);
                            return v___x_1452_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_x_1437_);
                    v___x_1453_ = lean_nat_add(v_m_1441_, v___x_1440_);
                    crate::leanh::lean_dec(v_m_1441_);
                    v___x_1454_ = lean_nat_dec_le(v___x_1453_, v_x_1438_);
                    if v___x_1454_ == 0 {
                        crate::leanh::lean_dec(v___x_1453_);
                        crate::leanh::lean_dec(v_x_1438_);
                        v___x_1455_ = crate::leanh::lean_box(0);
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
    mut v_as_1457_: *mut crate::leanh::LeanObject,
    mut v_k_1458_: *mut crate::leanh::LeanObject,
    mut v_x_1459_: *mut crate::leanh::LeanObject,
    mut v_x_1460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1461_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v_as_1457_, v_k_1458_, v_x_1459_, v_x_1460_);
    crate::leanh::lean_dec_ref(v_k_1458_);
    crate::leanh::lean_dec_ref(v_as_1457_);
    return v_res_1461_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(
    mut v_s_1462_: *mut crate::leanh::LeanObject,
    mut v_env_1463_: *mut crate::leanh::LeanObject,
    mut v_c_1464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v_snd_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1465_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1463_, v_c_1464_);
                if crate::leanh::lean_obj_tag(v___x_1465_) == 0 {
                    crate::leanh::lean_dec(v_c_1464_);
                    v___x_1466_ = crate::leanh::lean_box(0);
                    return v___x_1466_;
                } else {
                    v_val_1467_ = crate::leanh::lean_ctor_get(v___x_1465_, 0);
                    crate::leanh::lean_inc(v_val_1467_);
                    crate::leanh::lean_dec_ref_known(v___x_1465_, 1);
                    v___x_1468_ = lean_array_get_size(v_s_1462_);
                    v___x_1469_ = lean_nat_dec_lt(v_val_1467_, v___x_1468_);
                    if v___x_1469_ == 0 {
                        crate::leanh::lean_dec(v_val_1467_);
                        crate::leanh::lean_dec(v_c_1464_);
                        v___x_1470_ = crate::leanh::lean_box(0);
                        return v___x_1470_;
                    } else {
                        v___x_1471_ = lean_array_fget_borrowed(v_s_1462_, v_val_1467_);
                        crate::leanh::lean_dec(v_val_1467_);
                        v___x_1472_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1473_ = lean_array_get_size(v___x_1471_);
                        v___x_1474_ = lean_nat_dec_lt(v___x_1472_, v___x_1473_);
                        if v___x_1474_ == 0 {
                            crate::leanh::lean_dec(v_c_1464_);
                            v___x_1475_ = crate::leanh::lean_box(0);
                            return v___x_1475_;
                        } else {
                            v___x_1476_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1477_ = lean_nat_sub(v___x_1473_, v___x_1476_);
                            v___x_1478_ = lean_nat_dec_le(v___x_1472_, v___x_1477_);
                            if v___x_1478_ == 0 {
                                crate::leanh::lean_dec(v___x_1477_);
                                crate::leanh::lean_dec(v_c_1464_);
                                v___x_1479_ = crate::leanh::lean_box(0);
                                return v___x_1479_;
                            } else {
                                v___x_1480_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0;
                                v___x_1481_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1481_, 0, v_c_1464_);
                                crate::leanh::lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                                v___x_1482_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v___x_1471_, v___x_1481_, v___x_1472_, v___x_1477_);
                                crate::leanh::lean_dec_ref_known(v___x_1481_, 2);
                                if crate::leanh::lean_obj_tag(v___x_1482_) == 0 {
                                    v___x_1483_ = crate::leanh::lean_box(0);
                                    return v___x_1483_;
                                } else {
                                    v_val_1484_ = crate::leanh::lean_ctor_get(v___x_1482_, 0);
                                    v_isSharedCheck_1492_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1482_)) as u8;
                                    if v_isSharedCheck_1492_ == 0 {
                                        v___x_1486_ = v___x_1482_;
                                        v_isShared_1487_ = v_isSharedCheck_1492_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_val_1484_);
                                        crate::leanh::lean_dec(v___x_1482_);
                                        v___x_1486_ = crate::leanh::lean_box(0);
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
                v_snd_1488_ = crate::leanh::lean_ctor_get(v_val_1484_, 1);
                crate::leanh::lean_inc(v_snd_1488_);
                crate::leanh::lean_dec(v_val_1484_);
                if v_isShared_1487_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1486_, 0, v_snd_1488_);
                    v___x_1490_ = v___x_1486_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_snd_1488_);
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
    mut v_s_1493_: *mut crate::leanh::LeanObject,
    mut v_env_1494_: *mut crate::leanh::LeanObject,
    mut v_c_1495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1496_ = l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(
        v_s_1493_,
        v_env_1494_,
        v_c_1495_,
    );
    crate::leanh::lean_dec_ref(v_env_1494_);
    crate::leanh::lean_dec_ref(v_s_1493_);
    return v_res_1496_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(
    mut v_as_1497_: *mut crate::leanh::LeanObject,
    mut v_k_1498_: *mut crate::leanh::LeanObject,
    mut v_x_1499_: *mut crate::leanh::LeanObject,
    mut v_x_1500_: *mut crate::leanh::LeanObject,
    mut v_x_1501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v_as_1497_, v_k_1498_, v_x_1499_, v_x_1500_);
    return v___x_1502_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___boxed(
    mut v_as_1503_: *mut crate::leanh::LeanObject,
    mut v_k_1504_: *mut crate::leanh::LeanObject,
    mut v_x_1505_: *mut crate::leanh::LeanObject,
    mut v_x_1506_: *mut crate::leanh::LeanObject,
    mut v_x_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(v_as_1503_, v_k_1504_, v_x_1505_, v_x_1506_, v_x_1507_);
    crate::leanh::lean_dec_ref(v_k_1504_);
    crate::leanh::lean_dec_ref(v_as_1503_);
    return v_res_1508_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_x_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1512_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_;
    return v___x_1512_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_x_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1514_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_x_1513_);
    crate::leanh::lean_dec_ref(v_x_1513_);
    return v_res_1514_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_x_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = crate::leanh::lean_box(0);
    return v___x_1516_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_x_1517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1518_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_x_1517_);
    crate::leanh::lean_dec_ref(v_x_1517_);
    return v_res_1518_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_s_1519_: *mut crate::leanh::LeanObject,
    mut v_x_1520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_1519_);
    return v_s_1519_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_s_1521_: *mut crate::leanh::LeanObject,
    mut v_x_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1523_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_s_1521_, v_x_1522_);
    crate::leanh::lean_dec_ref(v_x_1522_);
    crate::leanh::lean_dec_ref(v_s_1521_);
    return v_res_1523_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_importedEntries_1524_: *mut crate::leanh::LeanObject,
    mut v___y_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1527_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1527_, 0, v_importedEntries_1524_);
    return v___x_1527_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_importedEntries_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1531_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_importedEntries_1528_, v___y_1529_);
    crate::leanh::lean_dec_ref(v___y_1529_);
    return v_res_1531_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_exportedEnv_1532_: *mut crate::leanh::LeanObject,
    mut v___x_1533_: u8,
    mut v_names_1534_: *mut crate::leanh::LeanObject,
    mut v_name_1535_: *mut crate::leanh::LeanObject,
    mut v_x_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_name_1535_);
    v___x_1537_ = l_Lean_Environment_find_x3f(v_exportedEnv_1532_, v_name_1535_, v___x_1533_);
    if crate::leanh::lean_obj_tag(v___x_1537_) == 0 {
        crate::leanh::lean_dec(v_name_1535_);
        return v_names_1534_;
    } else {
        let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_1537_, 1);
        v___x_1538_ = lean_array_push(v_names_1534_, v_name_1535_);
        return v___x_1538_;
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_exportedEnv_1539_: *mut crate::leanh::LeanObject,
    mut v___x_1540_: *mut crate::leanh::LeanObject,
    mut v_names_1541_: *mut crate::leanh::LeanObject,
    mut v_name_1542_: *mut crate::leanh::LeanObject,
    mut v_x_1543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1738__boxed_1544_: u8 = 0;
    let mut v_res_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1738__boxed_1544_ = (crate::leanh::lean_unbox(v___x_1540_) as u8);
    v_res_1545_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_exportedEnv_1539_, v___x_1738__boxed_1544_, v_names_1541_, v_name_1542_, v_x_1543_);
    crate::leanh::lean_dec_ref(v_x_1543_);
    return v_res_1545_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__1(
    mut v_s_1546_: *mut crate::leanh::LeanObject,
    mut v_sz_1547_: usize,
    mut v_i_1548_: usize,
    mut v_bs_1549_: *mut crate::leanh::LeanObject,
    mut v___y_1550_: *mut crate::leanh::LeanObject,
    mut v___y_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1561_: u8 = 0;
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: usize = 0;
    let mut v___x_1567_: usize = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1552_ = lean_usize_dec_lt(v_i_1548_, v_sz_1547_);
                if v___x_1552_ == 0 {
                    crate::leanh::lean_dec_ref(v_s_1546_);
                    v___x_1553_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1553_, 0, v_bs_1549_);
                    crate::leanh::lean_ctor_set(v___x_1553_, 1, v___y_1551_);
                    return v___x_1553_;
                } else {
                    v_v_1554_ = lean_array_uget(v_bs_1549_, v_i_1548_);
                    crate::leanh::lean_inc_ref(v_s_1546_);
                    v___x_1555_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed as *mut core::ffi::c_void, 3, 1);
                    crate::leanh::lean_closure_set(v___x_1555_, 0, v_s_1546_);
                    crate::leanh::lean_inc(v_v_1554_);
                    v___x_1556_ =
                        l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(
                            v___x_1555_,
                            v_v_1554_,
                            v___y_1550_,
                            v___y_1551_,
                        );
                    v_fst_1557_ = crate::leanh::lean_ctor_get(v___x_1556_, 0);
                    v_snd_1558_ = crate::leanh::lean_ctor_get(v___x_1556_, 1);
                    v_isSharedCheck_1571_ = (!crate::leanh::lean_is_exclusive(v___x_1556_)) as u8;
                    if v_isSharedCheck_1571_ == 0 {
                        v___x_1560_ = v___x_1556_;
                        v_isShared_1561_ = v_isSharedCheck_1571_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1558_);
                        crate::leanh::lean_inc(v_fst_1557_);
                        crate::leanh::lean_dec(v___x_1556_);
                        v___x_1560_ = crate::leanh::lean_box(0);
                        v_isShared_1561_ = v_isSharedCheck_1571_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1562_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_1563_ = lean_array_uset(v_bs_1549_, v_i_1548_, v___x_1562_);
                if v_isShared_1561_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1560_, 1, v_fst_1557_);
                    crate::leanh::lean_ctor_set(v___x_1560_, 0, v_v_1554_);
                    v___x_1565_ = v___x_1560_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_v_1554_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_fst_1557_);
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
    mut v_s_1572_: *mut crate::leanh::LeanObject,
    mut v_sz_1573_: *mut crate::leanh::LeanObject,
    mut v_i_1574_: *mut crate::leanh::LeanObject,
    mut v_bs_1575_: *mut crate::leanh::LeanObject,
    mut v___y_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1578_: usize = 0;
    let mut v_i_boxed_1579_: usize = 0;
    let mut v_res_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1578_ = crate::leanh::lean_unbox_usize(v_sz_1573_);
    crate::leanh::lean_dec(v_sz_1573_);
    v_i_boxed_1579_ = crate::leanh::lean_unbox_usize(v_i_1574_);
    crate::leanh::lean_dec(v_i_1574_);
    v_res_1580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__1(v_s_1572_, v_sz_boxed_1578_, v_i_boxed_1579_, v_bs_1575_, v___y_1576_, v___y_1577_);
    crate::leanh::lean_dec_ref(v___y_1576_);
    return v_res_1580_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_f_1581_: *mut crate::leanh::LeanObject,
    mut v_keys_1582_: *mut crate::leanh::LeanObject,
    mut v_vals_1583_: *mut crate::leanh::LeanObject,
    mut v_i_1584_: *mut crate::leanh::LeanObject,
    mut v_acc_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    let mut v_k_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1586_ = lean_array_get_size(v_keys_1582_);
                v___x_1587_ = lean_nat_dec_lt(v_i_1584_, v___x_1586_);
                if v___x_1587_ == 0 {
                    crate::leanh::lean_dec(v_i_1584_);
                    crate::leanh::lean_dec(v_f_1581_);
                    return v_acc_1585_;
                } else {
                    v_k_1588_ = lean_array_fget_borrowed(v_keys_1582_, v_i_1584_);
                    v_v_1589_ = lean_array_fget_borrowed(v_vals_1583_, v_i_1584_);
                    crate::leanh::lean_inc(v_f_1581_);
                    crate::leanh::lean_inc(v_v_1589_);
                    crate::leanh::lean_inc(v_k_1588_);
                    v___x_1590_ =
                        crate::leanh::lean_apply_3(v_f_1581_, v_acc_1585_, v_k_1588_, v_v_1589_);
                    v___x_1591_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1592_ = lean_nat_add(v_i_1584_, v___x_1591_);
                    crate::leanh::lean_dec(v_i_1584_);
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
    mut v_f_1594_: *mut crate::leanh::LeanObject,
    mut v_keys_1595_: *mut crate::leanh::LeanObject,
    mut v_vals_1596_: *mut crate::leanh::LeanObject,
    mut v_i_1597_: *mut crate::leanh::LeanObject,
    mut v_acc_1598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1599_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_1594_, v_keys_1595_, v_vals_1596_, v_i_1597_, v_acc_1598_);
    crate::leanh::lean_dec_ref(v_vals_1596_);
    crate::leanh::lean_dec_ref(v_keys_1595_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_f_1600_: *mut crate::leanh::LeanObject,
    mut v_x_1601_: *mut crate::leanh::LeanObject,
    mut v_x_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1601_) == 0 {
        let mut v_es_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: u8 = 0;
        v_es_1603_ = crate::leanh::lean_ctor_get(v_x_1601_, 0);
        v___x_1604_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1605_ = lean_array_get_size(v_es_1603_);
        v___x_1606_ = lean_nat_dec_lt(v___x_1604_, v___x_1605_);
        if v___x_1606_ == 0 {
            crate::leanh::lean_dec(v_f_1600_);
            return v_x_1602_;
        } else {
            let mut v___x_1607_: u8 = 0;
            v___x_1607_ = lean_nat_dec_le(v___x_1605_, v___x_1605_);
            if v___x_1607_ == 0 {
                if v___x_1606_ == 0 {
                    crate::leanh::lean_dec(v_f_1600_);
                    return v_x_1602_;
                } else {
                    let mut v___x_1608_: usize = 0;
                    let mut v___x_1609_: usize = 0;
                    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_1608_ = 0usize;
                    v___x_1609_ = lean_usize_of_nat(v___x_1605_);
                    v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1600_, v_es_1603_, v___x_1608_, v___x_1609_, v_x_1602_);
                    return v___x_1610_;
                }
            } else {
                let mut v___x_1611_: usize = 0;
                let mut v___x_1612_: usize = 0;
                let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_1611_ = 0usize;
                v___x_1612_ = lean_usize_of_nat(v___x_1605_);
                v___x_1613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1600_, v_es_1603_, v___x_1611_, v___x_1612_, v_x_1602_);
                return v___x_1613_;
            }
        }
    } else {
        let mut v_ks_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_1614_ = crate::leanh::lean_ctor_get(v_x_1601_, 0);
        v_vs_1615_ = crate::leanh::lean_ctor_get(v_x_1601_, 1);
        v___x_1616_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_1617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_1600_, v_ks_1614_, v_vs_1615_, v___x_1616_, v_x_1602_);
        return v___x_1617_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_f_1618_: *mut crate::leanh::LeanObject,
    mut v_as_1619_: *mut crate::leanh::LeanObject,
    mut v_i_1620_: usize,
    mut v_stop_1621_: usize,
    mut v_b_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: usize = 0;
    let mut v___x_1626_: usize = 0;
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1628_ = lean_usize_dec_eq(v_i_1620_, v_stop_1621_);
                if v___x_1628_ == 0 {
                    v___x_1629_ = lean_array_uget_borrowed(v_as_1619_, v_i_1620_);
                    match crate::leanh::lean_obj_tag(v___x_1629_) {
                        0 => {
                            v_key_1630_ = crate::leanh::lean_ctor_get(v___x_1629_, 0);
                            v_val_1631_ = crate::leanh::lean_ctor_get(v___x_1629_, 1);
                            crate::leanh::lean_inc(v_f_1618_);
                            crate::leanh::lean_inc(v_val_1631_);
                            crate::leanh::lean_inc(v_key_1630_);
                            v___x_1632_ = crate::leanh::lean_apply_3(
                                v_f_1618_,
                                v_b_1622_,
                                v_key_1630_,
                                v_val_1631_,
                            );
                            v___y_1624_ = v___x_1632_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_1633_ = crate::leanh::lean_ctor_get(v___x_1629_, 0);
                            crate::leanh::lean_inc(v_f_1618_);
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
                    crate::leanh::lean_dec(v_f_1618_);
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
    mut v_f_1635_: *mut crate::leanh::LeanObject,
    mut v_as_1636_: *mut crate::leanh::LeanObject,
    mut v_i_1637_: *mut crate::leanh::LeanObject,
    mut v_stop_1638_: *mut crate::leanh::LeanObject,
    mut v_b_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1640_: usize = 0;
    let mut v_stop_boxed_1641_: usize = 0;
    let mut v_res_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1640_ = crate::leanh::lean_unbox_usize(v_i_1637_);
    crate::leanh::lean_dec(v_i_1637_);
    v_stop_boxed_1641_ = crate::leanh::lean_unbox_usize(v_stop_1638_);
    crate::leanh::lean_dec(v_stop_1638_);
    v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1635_, v_as_1636_, v_i_boxed_1640_, v_stop_boxed_1641_, v_b_1639_);
    crate::leanh::lean_dec_ref(v_as_1636_);
    return v_res_1642_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_1643_: *mut crate::leanh::LeanObject,
    mut v_x_1644_: *mut crate::leanh::LeanObject,
    mut v_x_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1643_, v_x_1644_, v_x_1645_);
    crate::leanh::lean_dec_ref(v_x_1644_);
    return v_res_1646_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg___lam__0(
    mut v_f_1647_: *mut crate::leanh::LeanObject,
    mut v_x1_1648_: *mut crate::leanh::LeanObject,
    mut v_x2_1649_: *mut crate::leanh::LeanObject,
    mut v_x3_1650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = crate::leanh::lean_apply_3(v_f_1647_, v_x1_1648_, v_x2_1649_, v_x3_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(
    mut v_map_1652_: *mut crate::leanh::LeanObject,
    mut v_f_1653_: *mut crate::leanh::LeanObject,
    mut v_init_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1655_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_1655_, 0, v_f_1653_);
    v___x_1656_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_1655_, v_map_1652_, v_init_1654_);
    return v___x_1656_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_map_1657_: *mut crate::leanh::LeanObject,
    mut v_f_1658_: *mut crate::leanh::LeanObject,
    mut v_init_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1660_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(v_map_1657_, v_f_1658_, v_init_1659_);
    crate::leanh::lean_dec_ref(v_map_1657_);
    return v_res_1660_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(
    mut v_hi_1661_: *mut crate::leanh::LeanObject,
    mut v_pivot_1662_: *mut crate::leanh::LeanObject,
    mut v_as_1663_: *mut crate::leanh::LeanObject,
    mut v_i_1664_: *mut crate::leanh::LeanObject,
    mut v_k_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1666_ = lean_nat_dec_lt(v_k_1665_, v_hi_1661_);
                if v___x_1666_ == 0 {
                    crate::leanh::lean_dec(v_k_1665_);
                    v___x_1667_ = lean_array_fswap(v_as_1663_, v_i_1664_, v_hi_1661_);
                    v___x_1668_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1668_, 0, v_i_1664_);
                    crate::leanh::lean_ctor_set(v___x_1668_, 1, v___x_1667_);
                    return v___x_1668_;
                } else {
                    v___x_1669_ = lean_array_fget_borrowed(v_as_1663_, v_k_1665_);
                    v_fst_1670_ = crate::leanh::lean_ctor_get(v___x_1669_, 0);
                    v_fst_1671_ = crate::leanh::lean_ctor_get(v_pivot_1662_, 0);
                    v___x_1672_ = l_Lean_Name_quickLt(v_fst_1670_, v_fst_1671_);
                    if v___x_1672_ == 0 {
                        v___x_1673_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1674_ = lean_nat_add(v_k_1665_, v___x_1673_);
                        crate::leanh::lean_dec(v_k_1665_);
                        v_k_1665_ = v___x_1674_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1676_ = lean_array_fswap(v_as_1663_, v_i_1664_, v_k_1665_);
                        v___x_1677_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1678_ = lean_nat_add(v_i_1664_, v___x_1677_);
                        crate::leanh::lean_dec(v_i_1664_);
                        v___x_1679_ = lean_nat_add(v_k_1665_, v___x_1677_);
                        crate::leanh::lean_dec(v_k_1665_);
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
    mut v_hi_1681_: *mut crate::leanh::LeanObject,
    mut v_pivot_1682_: *mut crate::leanh::LeanObject,
    mut v_as_1683_: *mut crate::leanh::LeanObject,
    mut v_i_1684_: *mut crate::leanh::LeanObject,
    mut v_k_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_1681_, v_pivot_1682_, v_as_1683_, v_i_1684_, v_k_1685_);
    crate::leanh::lean_dec_ref(v_pivot_1682_);
    crate::leanh::lean_dec(v_hi_1681_);
    return v_res_1686_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(
    mut v_n_1687_: *mut crate::leanh::LeanObject,
    mut v_as_1688_: *mut crate::leanh::LeanObject,
    mut v_lo_1689_: *mut crate::leanh::LeanObject,
    mut v_hi_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: u8 = 0;
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1702_ = lean_nat_dec_lt(v_lo_1689_, v_hi_1690_);
                if v___x_1702_ == 0 {
                    crate::leanh::lean_dec(v_lo_1689_);
                    return v_as_1688_;
                } else {
                    v___x_1703_ = lean_nat_add(v_lo_1689_, v_hi_1690_);
                    v___x_1704_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_1705_ = lean_nat_shiftr(v___x_1703_, v___x_1704_);
                    crate::leanh::lean_dec(v___x_1703_);
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
                crate::leanh::lean_inc_n(v_lo_1689_, 2);
                v___x_1694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_1690_, v_pivot_1693_, v___y_1692_, v_lo_1689_, v_lo_1689_);
                crate::leanh::lean_dec(v_pivot_1693_);
                v_fst_1695_ = crate::leanh::lean_ctor_get(v___x_1694_, 0);
                crate::leanh::lean_inc(v_fst_1695_);
                v_snd_1696_ = crate::leanh::lean_ctor_get(v___x_1694_, 1);
                crate::leanh::lean_inc(v_snd_1696_);
                crate::leanh::lean_dec_ref(v___x_1694_);
                v___x_1697_ = lean_nat_dec_le(v_hi_1690_, v_fst_1695_);
                if v___x_1697_ == 0 {
                    v___x_1698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v_n_1687_, v_snd_1696_, v_lo_1689_, v_fst_1695_);
                    v___x_1699_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1700_ = lean_nat_add(v_fst_1695_, v___x_1699_);
                    crate::leanh::lean_dec(v_fst_1695_);
                    v_as_1688_ = v___x_1698_;
                    v_lo_1689_ = v___x_1700_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1695_);
                    crate::leanh::lean_dec(v_lo_1689_);
                    return v_snd_1696_;
                }
            }
            2 => {
                v___x_1708_ = lean_array_fget_borrowed(v___y_1707_, v_mid_1705_);
                v___x_1709_ = lean_array_fget_borrowed(v___y_1707_, v_hi_1690_);
                v___x_1710_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_1708_, v___x_1709_);
                if v___x_1710_ == 0 {
                    crate::leanh::lean_dec(v_mid_1705_);
                    v___y_1692_ = v___y_1707_;
                    state = 1;
                    continue;
                } else {
                    v___x_1711_ = lean_array_fswap(v___y_1707_, v_mid_1705_, v_hi_1690_);
                    crate::leanh::lean_dec(v_mid_1705_);
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
    mut v_n_1722_: *mut crate::leanh::LeanObject,
    mut v_as_1723_: *mut crate::leanh::LeanObject,
    mut v_lo_1724_: *mut crate::leanh::LeanObject,
    mut v_hi_1725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v_n_1722_, v_as_1723_, v_lo_1724_, v_hi_1725_);
    crate::leanh::lean_dec(v_hi_1725_);
    crate::leanh::lean_dec(v_n_1722_);
    return v_res_1726_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v___x_1729_: *mut crate::leanh::LeanObject,
    mut v_env_1730_: *mut crate::leanh::LeanObject,
    mut v_s_1731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_checked_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_constants_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v_exportedEnv_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_privateEnv_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_allNames_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1744_: usize = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: u8 = 0;
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_checked_1732_ = crate::leanh::lean_ctor_get(v_env_1730_, 2);
                crate::leanh::lean_inc_ref(v_checked_1732_);
                v___x_1733_ = lean_task_get_own(v_checked_1732_);
                v_constants_1734_ = crate::leanh::lean_ctor_get(v___x_1733_, 0);
                crate::leanh::lean_inc_ref(v_constants_1734_);
                crate::leanh::lean_dec(v___x_1733_);
                v_map_u2082_1735_ = crate::leanh::lean_ctor_get(v_constants_1734_, 1);
                crate::leanh::lean_inc_ref(v_map_u2082_1735_);
                crate::leanh::lean_dec_ref(v_constants_1734_);
                v___x_1736_ = 1;
                crate::leanh::lean_inc_ref(v_env_1730_);
                v_exportedEnv_1737_ = l_Lean_Environment_setExporting(v_env_1730_, v___x_1736_);
                v___x_1738_ = 0;
                v___x_1739_ = crate::leanh::lean_box((v___x_1738_) as usize);
                v___f_1740_ = crate::leanh::lean_alloc_closure(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 5, 2);
                crate::leanh::lean_closure_set(v___f_1740_, 0, v_exportedEnv_1737_);
                crate::leanh::lean_closure_set(v___f_1740_, 1, v___x_1739_);
                v_privateEnv_1741_ = l_Lean_Environment_setExporting(v_env_1730_, v___x_1738_);
                v___x_1742_ = lean_mk_empty_array_with_capacity(v___x_1729_);
                v_allNames_1743_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(v_map_u2082_1735_, v___f_1740_, v___x_1742_);
                crate::leanh::lean_dec_ref(v_map_u2082_1735_);
                v_sz_1744_ = lean_array_size(v_allNames_1743_);
                v___x_1745_ = crate::leanh::lean_box_usize(v_sz_1744_);
                v___x_1746_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_;
                v___x_1747_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__1___boxed as *mut core::ffi::c_void, 6, 4);
                crate::leanh::lean_closure_set(v___x_1747_, 0, v_s_1731_);
                crate::leanh::lean_closure_set(v___x_1747_, 1, v___x_1745_);
                crate::leanh::lean_closure_set(v___x_1747_, 2, v___x_1746_);
                crate::leanh::lean_closure_set(v___x_1747_, 3, v_allNames_1743_);
                v_entries_1748_ =
                    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
                        v_privateEnv_1741_,
                        v___x_1747_,
                    );
                v___x_1749_ = lean_array_get_size(v_entries_1748_);
                v___x_1755_ = lean_nat_dec_eq(v___x_1749_, v___x_1729_);
                if v___x_1755_ == 0 {
                    v___x_1756_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1757_ = lean_nat_sub(v___x_1749_, v___x_1756_);
                    v___x_1761_ = lean_nat_dec_le(v___x_1729_, v___x_1757_);
                    if v___x_1761_ == 0 {
                        crate::leanh::lean_dec(v___x_1729_);
                        crate::leanh::lean_inc(v___x_1757_);
                        v___y_1759_ = v___x_1757_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1759_ = v___x_1729_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1729_);
                    crate::leanh::lean_inc_n(v_entries_1748_, 2);
                    v___x_1762_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1762_, 0, v_entries_1748_);
                    crate::leanh::lean_ctor_set(v___x_1762_, 1, v_entries_1748_);
                    crate::leanh::lean_ctor_set(v___x_1762_, 2, v_entries_1748_);
                    return v___x_1762_;
                }
            }
            1 => {
                v___x_1753_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v___x_1749_, v_entries_1748_, v___y_1751_, v___y_1752_);
                crate::leanh::lean_dec(v___y_1752_);
                crate::leanh::lean_inc_ref_n(v___x_1753_, 2);
                v___x_1754_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1754_, 0, v___x_1753_);
                crate::leanh::lean_ctor_set(v___x_1754_, 1, v___x_1753_);
                crate::leanh::lean_ctor_set(v___x_1754_, 2, v___x_1753_);
                return v___x_1754_;
            }
            2 => {
                v___x_1760_ = lean_nat_dec_le(v___y_1759_, v___x_1757_);
                if v___x_1760_ == 0 {
                    crate::leanh::lean_dec(v___x_1757_);
                    crate::leanh::lean_inc(v___y_1759_);
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
    mut v___x_1763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1765_, 0, v___x_1763_);
    return v___x_1765_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v___x_1766_: *mut crate::leanh::LeanObject,
    mut v___y_1767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v___x_1766_);
    return v_res_1768_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_;
    v___x_1817_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1816_);
    return v___x_1817_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_a_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1819_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_();
    return v_res_1819_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0(
    mut v_00_u03c3_1820_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1821_: *mut crate::leanh::LeanObject,
    mut v_map_1822_: *mut crate::leanh::LeanObject,
    mut v_f_1823_: *mut crate::leanh::LeanObject,
    mut v_init_1824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(v_map_1822_, v_f_1823_, v_init_1824_);
    return v___x_1825_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03c3_1826_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1827_: *mut crate::leanh::LeanObject,
    mut v_map_1828_: *mut crate::leanh::LeanObject,
    mut v_f_1829_: *mut crate::leanh::LeanObject,
    mut v_init_1830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1831_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0(v_00_u03c3_1826_, v_00_u03b2_1827_, v_map_1828_, v_f_1829_, v_init_1830_);
    crate::leanh::lean_dec_ref(v_map_1828_);
    return v_res_1831_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2(
    mut v_n_1832_: *mut crate::leanh::LeanObject,
    mut v_as_1833_: *mut crate::leanh::LeanObject,
    mut v_lo_1834_: *mut crate::leanh::LeanObject,
    mut v_hi_1835_: *mut crate::leanh::LeanObject,
    mut v_w_1836_: *mut crate::leanh::LeanObject,
    mut v_hlo_1837_: *mut crate::leanh::LeanObject,
    mut v_hhi_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v_n_1832_, v_as_1833_, v_lo_1834_, v_hi_1835_);
    return v___x_1839_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___boxed(
    mut v_n_1840_: *mut crate::leanh::LeanObject,
    mut v_as_1841_: *mut crate::leanh::LeanObject,
    mut v_lo_1842_: *mut crate::leanh::LeanObject,
    mut v_hi_1843_: *mut crate::leanh::LeanObject,
    mut v_w_1844_: *mut crate::leanh::LeanObject,
    mut v_hlo_1845_: *mut crate::leanh::LeanObject,
    mut v_hhi_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2(v_n_1840_, v_as_1841_, v_lo_1842_, v_hi_1843_, v_w_1844_, v_hlo_1845_, v_hhi_1846_);
    crate::leanh::lean_dec(v_hi_1843_);
    crate::leanh::lean_dec(v_n_1840_);
    return v_res_1847_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_map_1848_: *mut crate::leanh::LeanObject,
    mut v_f_1849_: *mut crate::leanh::LeanObject,
    mut v_init_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1849_, v_map_1848_, v_init_1850_);
    return v___x_1851_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_map_1852_: *mut crate::leanh::LeanObject,
    mut v_f_1853_: *mut crate::leanh::LeanObject,
    mut v_init_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_1852_, v_f_1853_, v_init_1854_);
    crate::leanh::lean_dec_ref(v_map_1852_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03c3_1856_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1857_: *mut crate::leanh::LeanObject,
    mut v_map_1858_: *mut crate::leanh::LeanObject,
    mut v_f_1859_: *mut crate::leanh::LeanObject,
    mut v_init_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1859_, v_map_1858_, v_init_1860_);
    return v___x_1861_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03c3_1862_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1863_: *mut crate::leanh::LeanObject,
    mut v_map_1864_: *mut crate::leanh::LeanObject,
    mut v_f_1865_: *mut crate::leanh::LeanObject,
    mut v_init_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_1862_, v_00_u03b2_1863_, v_map_1864_, v_f_1865_, v_init_1866_);
    crate::leanh::lean_dec_ref(v_map_1864_);
    return v_res_1867_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3(
    mut v_n_1868_: *mut crate::leanh::LeanObject,
    mut v_lo_1869_: *mut crate::leanh::LeanObject,
    mut v_hi_1870_: *mut crate::leanh::LeanObject,
    mut v_hhi_1871_: *mut crate::leanh::LeanObject,
    mut v_pivot_1872_: *mut crate::leanh::LeanObject,
    mut v_as_1873_: *mut crate::leanh::LeanObject,
    mut v_i_1874_: *mut crate::leanh::LeanObject,
    mut v_k_1875_: *mut crate::leanh::LeanObject,
    mut v_ilo_1876_: *mut crate::leanh::LeanObject,
    mut v_ik_1877_: *mut crate::leanh::LeanObject,
    mut v_w_1878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_1870_, v_pivot_1872_, v_as_1873_, v_i_1874_, v_k_1875_);
    return v___x_1879_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___boxed(
    mut v_n_1880_: *mut crate::leanh::LeanObject,
    mut v_lo_1881_: *mut crate::leanh::LeanObject,
    mut v_hi_1882_: *mut crate::leanh::LeanObject,
    mut v_hhi_1883_: *mut crate::leanh::LeanObject,
    mut v_pivot_1884_: *mut crate::leanh::LeanObject,
    mut v_as_1885_: *mut crate::leanh::LeanObject,
    mut v_i_1886_: *mut crate::leanh::LeanObject,
    mut v_k_1887_: *mut crate::leanh::LeanObject,
    mut v_ilo_1888_: *mut crate::leanh::LeanObject,
    mut v_ik_1889_: *mut crate::leanh::LeanObject,
    mut v_w_1890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3(v_n_1880_, v_lo_1881_, v_hi_1882_, v_hhi_1883_, v_pivot_1884_, v_as_1885_, v_i_1886_, v_k_1887_, v_ilo_1888_, v_ik_1889_, v_w_1890_);
    crate::leanh::lean_dec_ref(v_pivot_1884_);
    crate::leanh::lean_dec(v_hi_1882_);
    crate::leanh::lean_dec(v_lo_1881_);
    crate::leanh::lean_dec(v_n_1880_);
    return v_res_1891_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03c3_1892_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1893_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1894_: *mut crate::leanh::LeanObject,
    mut v_f_1895_: *mut crate::leanh::LeanObject,
    mut v_x_1896_: *mut crate::leanh::LeanObject,
    mut v_x_1897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1895_, v_x_1896_, v_x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_1899_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1900_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1901_: *mut crate::leanh::LeanObject,
    mut v_f_1902_: *mut crate::leanh::LeanObject,
    mut v_x_1903_: *mut crate::leanh::LeanObject,
    mut v_x_1904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_1899_, v_00_u03b1_1900_, v_00_u03b2_1901_, v_f_1902_, v_x_1903_, v_x_1904_);
    crate::leanh::lean_dec_ref(v_x_1903_);
    return v_res_1905_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1906_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1907_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1908_: *mut crate::leanh::LeanObject,
    mut v_f_1909_: *mut crate::leanh::LeanObject,
    mut v_as_1910_: *mut crate::leanh::LeanObject,
    mut v_i_1911_: usize,
    mut v_stop_1912_: usize,
    mut v_b_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1909_, v_as_1910_, v_i_1911_, v_stop_1912_, v_b_1913_);
    return v___x_1914_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1915_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1916_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1917_: *mut crate::leanh::LeanObject,
    mut v_f_1918_: *mut crate::leanh::LeanObject,
    mut v_as_1919_: *mut crate::leanh::LeanObject,
    mut v_i_1920_: *mut crate::leanh::LeanObject,
    mut v_stop_1921_: *mut crate::leanh::LeanObject,
    mut v_b_1922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1923_: usize = 0;
    let mut v_stop_boxed_1924_: usize = 0;
    let mut v_res_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1923_ = crate::leanh::lean_unbox_usize(v_i_1920_);
    crate::leanh::lean_dec(v_i_1920_);
    v_stop_boxed_1924_ = crate::leanh::lean_unbox_usize(v_stop_1921_);
    crate::leanh::lean_dec(v_stop_1921_);
    v_res_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1915_, v_00_u03b2_1916_, v_00_u03c3_1917_, v_f_1918_, v_as_1919_, v_i_boxed_1923_, v_stop_boxed_1924_, v_b_1922_);
    crate::leanh::lean_dec_ref(v_as_1919_);
    return v_res_1925_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03c3_1926_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1927_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1928_: *mut crate::leanh::LeanObject,
    mut v_f_1929_: *mut crate::leanh::LeanObject,
    mut v_keys_1930_: *mut crate::leanh::LeanObject,
    mut v_vals_1931_: *mut crate::leanh::LeanObject,
    mut v_heq_1932_: *mut crate::leanh::LeanObject,
    mut v_i_1933_: *mut crate::leanh::LeanObject,
    mut v_acc_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1935_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_1929_, v_keys_1930_, v_vals_1931_, v_i_1933_, v_acc_1934_);
    return v___x_1935_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03c3_1936_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1937_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1938_: *mut crate::leanh::LeanObject,
    mut v_f_1939_: *mut crate::leanh::LeanObject,
    mut v_keys_1940_: *mut crate::leanh::LeanObject,
    mut v_vals_1941_: *mut crate::leanh::LeanObject,
    mut v_heq_1942_: *mut crate::leanh::LeanObject,
    mut v_i_1943_: *mut crate::leanh::LeanObject,
    mut v_acc_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_1936_, v_00_u03b1_1937_, v_00_u03b2_1938_, v_f_1939_, v_keys_1940_, v_vals_1941_, v_heq_1942_, v_i_1943_, v_acc_1944_);
    crate::leanh::lean_dec_ref(v_vals_1941_);
    crate::leanh::lean_dec_ref(v_keys_1940_);
    return v_res_1945_;
}
pub unsafe fn l_Lean_collectAxioms___redArg___lam__0(
    mut v___x_1946_: *mut crate::leanh::LeanObject,
    mut v_constName_1947_: *mut crate::leanh::LeanObject,
    mut v_toPure_1948_: *mut crate::leanh::LeanObject,
    mut v_env_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1950_: u8 = 0;
    let mut v_privateEnv_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1950_ = 0;
    crate::leanh::lean_inc_ref(v_env_1949_);
    v_privateEnv_1951_ = l_Lean_Environment_setExporting(v_env_1949_, v___x_1950_);
    v___x_1952_ = l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt;
    v___x_1953_ = crate::leanh::lean_box(2);
    v___x_1954_ = crate::leanh::lean_box(0);
    v_s_1955_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_1946_,
        v___x_1952_,
        v_env_1949_,
        v___x_1953_,
        v___x_1954_,
    );
    v___x_1956_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1956_, 0, v_s_1955_);
    v___x_1957_ = crate::leanh::lean_alloc_closure(
        l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1957_, 0, v___x_1956_);
    crate::leanh::lean_closure_set(v___x_1957_, 1, v_constName_1947_);
    v___x_1958_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
        v_privateEnv_1951_,
        v___x_1957_,
    );
    v___x_1959_ =
        crate::leanh::lean_apply_2(v_toPure_1948_, crate::leanh::lean_box(0), v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn l_Lean_collectAxioms___redArg(
    mut v_inst_1960_: *mut crate::leanh::LeanObject,
    mut v_inst_1961_: *mut crate::leanh::LeanObject,
    mut v_constName_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1963_ = crate::leanh::lean_ctor_get(v_inst_1960_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1963_);
    v_toBind_1964_ = crate::leanh::lean_ctor_get(v_inst_1960_, 1);
    crate::leanh::lean_inc(v_toBind_1964_);
    crate::leanh::lean_dec_ref(v_inst_1960_);
    v_getEnv_1965_ = crate::leanh::lean_ctor_get(v_inst_1961_, 0);
    crate::leanh::lean_inc(v_getEnv_1965_);
    crate::leanh::lean_dec_ref(v_inst_1961_);
    v_toPure_1966_ = crate::leanh::lean_ctor_get(v_toApplicative_1963_, 1);
    crate::leanh::lean_inc(v_toPure_1966_);
    crate::leanh::lean_dec_ref(v_toApplicative_1963_);
    v___x_1967_ = l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState;
    v___f_1968_ = crate::leanh::lean_alloc_closure(
        l_Lean_collectAxioms___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1968_, 0, v___x_1967_);
    crate::leanh::lean_closure_set(v___f_1968_, 1, v_constName_1962_);
    crate::leanh::lean_closure_set(v___f_1968_, 2, v_toPure_1966_);
    v___x_1969_ = crate::leanh::lean_apply_4(
        v_toBind_1964_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_getEnv_1965_,
        v___f_1968_,
    );
    return v___x_1969_;
}
pub unsafe fn l_Lean_collectAxioms(
    mut v_m_1970_: *mut crate::leanh::LeanObject,
    mut v_inst_1971_: *mut crate::leanh::LeanObject,
    mut v_inst_1972_: *mut crate::leanh::LeanObject,
    mut v_constName_1973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1974_ = l_Lean_collectAxioms___redArg(v_inst_1971_, v_inst_1972_, v_constName_1973_);
    return v___x_1974_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_CollectAxioms(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_MonadEnv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt,
    );
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_CollectAxioms(
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
pub unsafe fn initialize_Lean_Util_CollectAxioms(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_MonadEnv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectAxioms(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_CollectAxioms(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_CollectAxioms(builtin);
}
