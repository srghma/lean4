// Lean compiler output
// Module: Lean.Util.CollectAxioms
// Imports: Lean.MonadEnv
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fswap, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub, lean_panic_fn_borrowed, lean_string_append,
    lean_task_get_own, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
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
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0_value:
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
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6_value) as *mut leanh::LeanObject;
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 46, 99, 111, 108, 108, 101, 99, 116, 65, 110, 100, 71, 101, 116, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 111, 108, 108, 101, 99, 116, 65, 110, 100, 71, 101, 116, 58, 32, 39, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [39, 32, 110, 111, 116, 32, 105, 110, 32, 115, 101, 101, 110, 32, 97, 102, 116, 101, 114, 32, 99, 111, 108, 108, 101, 99, 116, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + core::mem::size_of::<usize>()*1) as u16, other: 1, tag: 0 }, m_objs: [(0 as *mut leanh::LeanObject)] };
pub static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 116, 105, 108, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__7_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__8_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11246366368068211756 as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 111, 108, 108, 101, 99, 116, 65, 120, 105, 111, 109, 115, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__9_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__10_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16007987903351044003 as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__11_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,4211746031378004846 as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__13_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14374199986448060823 as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 120, 112, 111, 114, 116, 101, 100, 65, 120, 105, 111, 109, 115, 69, 120, 116, 0]};
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__14_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__15_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14140705196984542656 as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanCtorObject<8> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__16_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__17_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__12_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__18_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = l_Lean_NameSet_empty;
    v___x_989_ = leanh::lean_box(1);
    v___x_990_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_990_, 0, v___x_989_);
    leanh::lean_ctor_set(v___x_990_, 1, v___x_988_);
    return v___x_990_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
    mut v_env_991_: *mut leanh::LeanObject,
    mut v_x_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0_once), _init_l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg___closed__0);
    v___x_994_ = leanh::lean_apply_2(v_x_992_, v_env_991_, v___x_993_);
    v_fst_995_ = leanh::lean_ctor_get(v___x_994_, 0);
    leanh::lean_inc(v_fst_995_);
    leanh::lean_dec_ref(v___x_994_);
    return v_fst_995_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM(
    mut v_00_u03b1_996_: *mut leanh::LeanObject,
    mut v_env_997_: *mut leanh::LeanObject,
    mut v_x_998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
        v_env_997_, v_x_998_,
    );
    return v___x_999_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(
    mut v_as_1000_: *mut leanh::LeanObject,
    mut v_i_1001_: usize,
    mut v_stop_1002_: usize,
    mut v_b_1003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: usize = 0;
    let mut v___x_1008_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1004_ = lean_usize_dec_eq(v_i_1001_, v_stop_1002_);
                if v___x_1004_ == 0 {
                    v___x_1005_ = lean_array_uget_borrowed(v_as_1000_, v_i_1001_);
                    leanh::lean_inc(v___x_1005_);
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
    mut v_as_1010_: *mut leanh::LeanObject,
    mut v_i_1011_: *mut leanh::LeanObject,
    mut v_stop_1012_: *mut leanh::LeanObject,
    mut v_b_1013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1014_: usize = 0;
    let mut v_stop_boxed_1015_: usize = 0;
    let mut v_res_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1014_ = leanh::lean_unbox_usize(v_i_1011_);
    leanh::lean_dec(v_i_1011_);
    v_stop_boxed_1015_ = leanh::lean_unbox_usize(v_stop_1012_);
    leanh::lean_dec(v_stop_1012_);
    v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_as_1010_, v_i_boxed_1014_, v_stop_boxed_1015_, v_b_1013_);
    leanh::lean_dec_ref(v_as_1010_);
    return v_res_1016_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
    mut v_s_1017_: *mut leanh::LeanObject,
    mut v_axs_1018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: u8 = 0;
    v___x_1019_ = leanh::lean_unsigned_to_nat(0);
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
                let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1023_ = 0usize;
                v___x_1024_ = lean_usize_of_nat(v___x_1020_);
                v___x_1025_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_axs_1018_, v___x_1023_, v___x_1024_, v_s_1017_);
                return v___x_1025_;
            }
        } else {
            let mut v___x_1026_: usize = 0;
            let mut v___x_1027_: usize = 0;
            let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1026_ = 0usize;
            v___x_1027_ = lean_usize_of_nat(v___x_1020_);
            v___x_1028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray_spec__0(v_axs_1018_, v___x_1026_, v___x_1027_, v_s_1017_);
            return v___x_1028_;
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray___boxed(
    mut v_s_1029_: *mut leanh::LeanObject,
    mut v_axs_1030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
        v_s_1029_,
        v_axs_1030_,
    );
    leanh::lean_dec_ref(v_axs_1030_);
    return v_res_1031_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(
    mut v_init_1032_: *mut leanh::LeanObject,
    mut v_x_1033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1033_) == 0 {
                    v_k_1034_ = leanh::lean_ctor_get(v_x_1033_, 1);
                    leanh::lean_inc(v_k_1034_);
                    v_l_1035_ = leanh::lean_ctor_get(v_x_1033_, 3);
                    leanh::lean_inc(v_l_1035_);
                    v_r_1036_ = leanh::lean_ctor_get(v_x_1033_, 4);
                    leanh::lean_inc(v_r_1036_);
                    leanh::lean_dec_ref_known(v_x_1033_, 5);
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
    mut v_hi_1040_: *mut leanh::LeanObject,
    mut v_pivot_1041_: *mut leanh::LeanObject,
    mut v_as_1042_: *mut leanh::LeanObject,
    mut v_i_1043_: *mut leanh::LeanObject,
    mut v_k_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1045_: u8 = 0;
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: u8 = 0;
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1045_ = lean_nat_dec_lt(v_k_1044_, v_hi_1040_);
                if v___x_1045_ == 0 {
                    leanh::lean_dec(v_k_1044_);
                    v___x_1046_ = lean_array_fswap(v_as_1042_, v_i_1043_, v_hi_1040_);
                    v___x_1047_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1047_, 0, v_i_1043_);
                    leanh::lean_ctor_set(v___x_1047_, 1, v___x_1046_);
                    return v___x_1047_;
                } else {
                    v___x_1048_ = lean_array_fget_borrowed(v_as_1042_, v_k_1044_);
                    v___x_1049_ = l_Lean_Name_lt(v___x_1048_, v_pivot_1041_);
                    if v___x_1049_ == 0 {
                        v___x_1050_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1051_ = lean_nat_add(v_k_1044_, v___x_1050_);
                        leanh::lean_dec(v_k_1044_);
                        v_k_1044_ = v___x_1051_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1053_ = lean_array_fswap(v_as_1042_, v_i_1043_, v_k_1044_);
                        v___x_1054_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1055_ = lean_nat_add(v_i_1043_, v___x_1054_);
                        leanh::lean_dec(v_i_1043_);
                        v___x_1056_ = lean_nat_add(v_k_1044_, v___x_1054_);
                        leanh::lean_dec(v_k_1044_);
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
    mut v_hi_1058_: *mut leanh::LeanObject,
    mut v_pivot_1059_: *mut leanh::LeanObject,
    mut v_as_1060_: *mut leanh::LeanObject,
    mut v_i_1061_: *mut leanh::LeanObject,
    mut v_k_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1063_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_1058_, v_pivot_1059_, v_as_1060_, v_i_1061_, v_k_1062_);
    leanh::lean_dec(v_pivot_1059_);
    leanh::lean_dec(v_hi_1058_);
    return v_res_1063_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(
    mut v_n_1064_: *mut leanh::LeanObject,
    mut v_as_1065_: *mut leanh::LeanObject,
    mut v_lo_1066_: *mut leanh::LeanObject,
    mut v_hi_1067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: u8 = 0;
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: u8 = 0;
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: u8 = 0;
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1079_ = lean_nat_dec_lt(v_lo_1066_, v_hi_1067_);
                if v___x_1079_ == 0 {
                    leanh::lean_dec(v_lo_1066_);
                    return v_as_1065_;
                } else {
                    v___x_1080_ = lean_nat_add(v_lo_1066_, v_hi_1067_);
                    v___x_1081_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_1082_ = lean_nat_shiftr(v___x_1080_, v___x_1081_);
                    leanh::lean_dec(v___x_1080_);
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
                leanh::lean_inc_n(v_lo_1066_, 2);
                v___x_1071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_1067_, v_pivot_1070_, v___y_1069_, v_lo_1066_, v_lo_1066_);
                leanh::lean_dec(v_pivot_1070_);
                v_fst_1072_ = leanh::lean_ctor_get(v___x_1071_, 0);
                leanh::lean_inc(v_fst_1072_);
                v_snd_1073_ = leanh::lean_ctor_get(v___x_1071_, 1);
                leanh::lean_inc(v_snd_1073_);
                leanh::lean_dec_ref(v___x_1071_);
                v___x_1074_ = lean_nat_dec_le(v_hi_1067_, v_fst_1072_);
                if v___x_1074_ == 0 {
                    v___x_1075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_1064_, v_snd_1073_, v_lo_1066_, v_fst_1072_);
                    v___x_1076_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1077_ = lean_nat_add(v_fst_1072_, v___x_1076_);
                    leanh::lean_dec(v_fst_1072_);
                    v_as_1065_ = v___x_1075_;
                    v_lo_1066_ = v___x_1077_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_1072_);
                    leanh::lean_dec(v_lo_1066_);
                    return v_snd_1073_;
                }
            }
            2 => {
                v___x_1085_ = lean_array_fget_borrowed(v___y_1084_, v_mid_1082_);
                v___x_1086_ = lean_array_fget_borrowed(v___y_1084_, v_hi_1067_);
                v___x_1087_ = l_Lean_Name_lt(v___x_1085_, v___x_1086_);
                if v___x_1087_ == 0 {
                    leanh::lean_dec(v_mid_1082_);
                    v___y_1069_ = v___y_1084_;
                    state = 1;
                    continue;
                } else {
                    v___x_1088_ = lean_array_fswap(v___y_1084_, v_mid_1082_, v_hi_1067_);
                    leanh::lean_dec(v_mid_1082_);
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
    mut v_n_1099_: *mut leanh::LeanObject,
    mut v_as_1100_: *mut leanh::LeanObject,
    mut v_lo_1101_: *mut leanh::LeanObject,
    mut v_hi_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1103_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_1099_, v_as_1100_, v_lo_1101_, v_hi_1102_);
    leanh::lean_dec(v_hi_1102_);
    leanh::lean_dec(v_n_1099_);
    return v_res_1103_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(
    mut v_extFind_x3f_1106_: *mut leanh::LeanObject,
    mut v_as_1107_: *mut leanh::LeanObject,
    mut v_i_1108_: usize,
    mut v_stop_1109_: usize,
    mut v_b_1110_: *mut leanh::LeanObject,
    mut v___y_1111_: *mut leanh::LeanObject,
    mut v___y_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1113_: u8 = 0;
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: usize = 0;
    let mut v___x_1119_: usize = 0;
    let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1113_ = lean_usize_dec_eq(v_i_1108_, v_stop_1109_);
                if v___x_1113_ == 0 {
                    v___x_1114_ = lean_array_uget_borrowed(v_as_1107_, v_i_1108_);
                    leanh::lean_inc(v___x_1114_);
                    leanh::lean_inc_ref(v_extFind_x3f_1106_);
                    v___x_1115_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
                        v_extFind_x3f_1106_,
                        v___x_1114_,
                        v___y_1111_,
                        v___y_1112_,
                    );
                    v_fst_1116_ = leanh::lean_ctor_get(v___x_1115_, 0);
                    leanh::lean_inc(v_fst_1116_);
                    v_snd_1117_ = leanh::lean_ctor_get(v___x_1115_, 1);
                    leanh::lean_inc(v_snd_1117_);
                    leanh::lean_dec_ref(v___x_1115_);
                    v___x_1118_ = 1usize;
                    v___x_1119_ = lean_usize_add(v_i_1108_, v___x_1118_);
                    v_i_1108_ = v___x_1119_;
                    v_b_1110_ = v_fst_1116_;
                    v___y_1112_ = v_snd_1117_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_extFind_x3f_1106_);
                    v___x_1121_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1121_, 0, v_b_1110_);
                    leanh::lean_ctor_set(v___x_1121_, 1, v___y_1112_);
                    return v___x_1121_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(
    mut v_extFind_x3f_1122_: *mut leanh::LeanObject,
    mut v_e_1123_: *mut leanh::LeanObject,
    mut v___y_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: u8 = 0;
    v___x_1126_ = l_Lean_Expr_getUsedConstants(v_e_1123_);
    v___x_1127_ = leanh::lean_unsigned_to_nat(0);
    v___x_1128_ = lean_array_get_size(v___x_1126_);
    v___x_1129_ = leanh::lean_box(0);
    v___x_1130_ = lean_nat_dec_lt(v___x_1127_, v___x_1128_);
    if v___x_1130_ == 0 {
        let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_1126_);
        leanh::lean_dec_ref(v_extFind_x3f_1122_);
        v___x_1131_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1131_, 0, v___x_1129_);
        leanh::lean_ctor_set(v___x_1131_, 1, v___y_1125_);
        return v___x_1131_;
    } else {
        let mut v___x_1132_: u8 = 0;
        v___x_1132_ = lean_nat_dec_le(v___x_1128_, v___x_1128_);
        if v___x_1132_ == 0 {
            if v___x_1130_ == 0 {
                let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___x_1126_);
                leanh::lean_dec_ref(v_extFind_x3f_1122_);
                v___x_1133_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1133_, 0, v___x_1129_);
                leanh::lean_ctor_set(v___x_1133_, 1, v___y_1125_);
                return v___x_1133_;
            } else {
                let mut v___x_1134_: usize = 0;
                let mut v___x_1135_: usize = 0;
                let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1134_ = 0usize;
                v___x_1135_ = lean_usize_of_nat(v___x_1128_);
                v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_1122_, v___x_1126_, v___x_1134_, v___x_1135_, v___x_1129_, v___y_1124_, v___y_1125_);
                leanh::lean_dec_ref(v___x_1126_);
                return v___x_1136_;
            }
        } else {
            let mut v___x_1137_: usize = 0;
            let mut v___x_1138_: usize = 0;
            let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1137_ = 0usize;
            v___x_1138_ = lean_usize_of_nat(v___x_1128_);
            v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_1122_, v___x_1126_, v___x_1137_, v___x_1138_, v___x_1129_, v___y_1124_, v___y_1125_);
            leanh::lean_dec_ref(v___x_1126_);
            return v___x_1139_;
        }
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
    mut v_extFind_x3f_1140_: *mut leanh::LeanObject,
    mut v_c_1141_: *mut leanh::LeanObject,
    mut v_a_1142_: *mut leanh::LeanObject,
    mut v_a_1143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_axioms_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1158_: u8 = 0;
    let mut v_seen_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_axioms_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___y_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_seen_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1170_: u8 = 0;
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1178_: u8 = 0;
    let mut v_unused_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: u8 = 0;
    let mut v___y_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___y_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_axioms_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_axioms_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_checked_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_extFind_x3f_1140_);
                leanh::lean_inc(v_c_1141_);
                leanh::lean_inc_ref(v_a_1142_);
                v___x_1144_ = leanh::lean_apply_2(v_extFind_x3f_1140_, v_a_1142_, v_c_1141_);
                if leanh::lean_obj_tag(v___x_1144_) == 1 {
                    leanh::lean_dec_ref(v_extFind_x3f_1140_);
                    v_val_1145_ = leanh::lean_ctor_get(v___x_1144_, 0);
                    leanh::lean_inc(v_val_1145_);
                    leanh::lean_dec_ref_known(v___x_1144_, 1);
                    v_seen_1146_ = leanh::lean_ctor_get(v_a_1143_, 0);
                    v_axioms_1147_ = leanh::lean_ctor_get(v_a_1143_, 1);
                    v_isSharedCheck_1158_ = (!leanh::lean_is_exclusive(v_a_1143_)) as u8;
                    if v_isSharedCheck_1158_ == 0 {
                        v___x_1149_ = v_a_1143_;
                        v_isShared_1150_ = v_isSharedCheck_1158_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_axioms_1147_);
                        leanh::lean_inc(v_seen_1146_);
                        leanh::lean_dec(v_a_1143_);
                        v___x_1149_ = leanh::lean_box(0);
                        v_isShared_1150_ = v_isSharedCheck_1158_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1144_);
                    v_seen_1159_ = leanh::lean_ctor_get(v_a_1143_, 0);
                    v_axioms_1160_ = leanh::lean_ctor_get(v_a_1143_, 1);
                    v_isSharedCheck_1265_ = (!leanh::lean_is_exclusive(v_a_1143_)) as u8;
                    if v_isSharedCheck_1265_ == 0 {
                        v___x_1162_ = v_a_1143_;
                        v_isShared_1163_ = v_isSharedCheck_1265_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_axioms_1160_);
                        leanh::lean_inc(v_seen_1159_);
                        leanh::lean_dec(v_a_1143_);
                        v___x_1162_ = leanh::lean_box(0);
                        v_isShared_1163_ = v_isSharedCheck_1265_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_val_1145_);
                v___x_1151_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_1141_, v_val_1145_, v_seen_1146_);
                v___x_1152_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
                    v_axioms_1147_,
                    v_val_1145_,
                );
                leanh::lean_dec(v_val_1145_);
                if v_isShared_1150_ == 0 {
                    leanh::lean_ctor_set(v___x_1149_, 1, v___x_1152_);
                    leanh::lean_ctor_set(v___x_1149_, 0, v___x_1151_);
                    v___x_1154_ = v___x_1149_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1157_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1151_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1152_);
                    v___x_1154_ = v_reuseFailAlloc_1157_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1155_ = leanh::lean_box(0);
                v___x_1156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1156_, 0, v___x_1155_);
                leanh::lean_ctor_set(v___x_1156_, 1, v___x_1154_);
                return v___x_1156_;
            }
            3 => {
                v___x_1214_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_seen_1159_, v_c_1141_);
                if leanh::lean_obj_tag(v___x_1214_) == 1 {
                    leanh::lean_dec(v_c_1141_);
                    leanh::lean_dec_ref(v_extFind_x3f_1140_);
                    v_val_1215_ = leanh::lean_ctor_get(v___x_1214_, 0);
                    leanh::lean_inc(v_val_1215_);
                    leanh::lean_dec_ref_known(v___x_1214_, 1);
                    v___x_1216_ =
                        l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
                            v_axioms_1160_,
                            v_val_1215_,
                        );
                    leanh::lean_dec(v_val_1215_);
                    if v_isShared_1163_ == 0 {
                        leanh::lean_ctor_set(v___x_1162_, 1, v___x_1216_);
                        v___x_1218_ = v___x_1162_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1221_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_seen_1159_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1216_);
                        v___x_1218_ = v_reuseFailAlloc_1221_;
                        state = 12;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1214_);
                    v_checked_1222_ = leanh::lean_ctor_get(v_a_1142_, 2);
                    v___x_1223_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0;
                    leanh::lean_inc(v_c_1141_);
                    v___x_1224_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_1141_, v___x_1223_, v_seen_1159_);
                    v___x_1225_ = l_Lean_NameSet_empty;
                    leanh::lean_inc(v___x_1224_);
                    if v_isShared_1163_ == 0 {
                        leanh::lean_ctor_set(v___x_1162_, 1, v___x_1225_);
                        leanh::lean_ctor_set(v___x_1162_, 0, v___x_1224_);
                        v___x_1227_ = v___x_1162_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1264_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1224_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1225_);
                        v___x_1227_ = v_reuseFailAlloc_1264_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v_seen_1167_ = leanh::lean_ctor_get(v___y_1165_, 0);
                v_isSharedCheck_1178_ = (!leanh::lean_is_exclusive(v___y_1165_)) as u8;
                if v_isSharedCheck_1178_ == 0 {
                    v_unused_1179_ = leanh::lean_ctor_get(v___y_1165_, 1);
                    leanh::lean_dec(v_unused_1179_);
                    v___x_1169_ = v___y_1165_;
                    v_isShared_1170_ = v_isSharedCheck_1178_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_seen_1167_);
                    leanh::lean_dec(v___y_1165_);
                    v___x_1169_ = leanh::lean_box(0);
                    v_isShared_1170_ = v_isSharedCheck_1178_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1171_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___y_1166_);
                v___x_1172_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_c_1141_, v___y_1166_, v_seen_1167_);
                v___x_1173_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_insertArray(
                    v_axioms_1160_,
                    v___y_1166_,
                );
                leanh::lean_dec_ref(v___y_1166_);
                if v_isShared_1170_ == 0 {
                    leanh::lean_ctor_set(v___x_1169_, 1, v___x_1173_);
                    leanh::lean_ctor_set(v___x_1169_, 0, v___x_1172_);
                    v___x_1175_ = v___x_1169_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1177_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1172_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1173_);
                    v___x_1175_ = v_reuseFailAlloc_1177_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1176_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1176_, 0, v___x_1171_);
                leanh::lean_ctor_set(v___x_1176_, 1, v___x_1175_);
                return v___x_1176_;
            }
            7 => {
                v___x_1186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v___y_1181_, v___y_1183_, v___y_1182_, v___y_1185_);
                leanh::lean_dec(v___y_1185_);
                leanh::lean_dec(v___y_1181_);
                v___y_1165_ = v___y_1184_;
                v___y_1166_ = v___x_1186_;
                state = 4;
                continue;
            }
            8 => {
                v___x_1193_ = lean_nat_dec_le(v___y_1192_, v___y_1189_);
                if v___x_1193_ == 0 {
                    leanh::lean_dec(v___y_1189_);
                    leanh::lean_inc(v___y_1192_);
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
                leanh::lean_dec(v___y_1197_);
                v___x_1199_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v___x_1198_, v___y_1195_);
                v___x_1200_ = lean_array_get_size(v___x_1199_);
                v___x_1201_ = leanh::lean_unsigned_to_nat(0);
                v___x_1202_ = lean_nat_dec_eq(v___x_1200_, v___x_1201_);
                if v___x_1202_ == 0 {
                    v___x_1203_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1204_ = lean_nat_sub(v___x_1200_, v___x_1203_);
                    v___x_1205_ = lean_nat_dec_le(v___x_1201_, v___x_1204_);
                    if v___x_1205_ == 0 {
                        leanh::lean_inc(v___x_1204_);
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
                if leanh::lean_obj_tag(v_axioms_1208_) == 0 {
                    v_size_1209_ = leanh::lean_ctor_get(v_axioms_1208_, 0);
                    leanh::lean_inc(v_size_1209_);
                    v___y_1195_ = v_axioms_1208_;
                    v___y_1196_ = v___y_1207_;
                    v___y_1197_ = v_size_1209_;
                    state = 9;
                    continue;
                } else {
                    v___x_1210_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1195_ = v_axioms_1208_;
                    v___y_1196_ = v___y_1207_;
                    v___y_1197_ = v___x_1210_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_axioms_1213_ = leanh::lean_ctor_get(v___y_1212_, 1);
                leanh::lean_inc(v_axioms_1213_);
                v___y_1207_ = v___y_1212_;
                v_axioms_1208_ = v_axioms_1213_;
                state = 10;
                continue;
            }
            12 => {
                v___x_1219_ = leanh::lean_box(0);
                v___x_1220_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1220_, 0, v___x_1219_);
                leanh::lean_ctor_set(v___x_1220_, 1, v___x_1218_);
                return v___x_1220_;
            }
            13 => {
                leanh::lean_inc_ref(v_checked_1222_);
                v___x_1228_ = lean_task_get_own(v_checked_1222_);
                leanh::lean_inc(v_c_1141_);
                v___x_1229_ = lean_environment_find(v___x_1228_, v_c_1141_);
                if leanh::lean_obj_tag(v___x_1229_) == 0 {
                    leanh::lean_dec(v___x_1224_);
                    leanh::lean_dec_ref(v_extFind_x3f_1140_);
                    v___y_1207_ = v___x_1227_;
                    v_axioms_1208_ = v___x_1225_;
                    state = 10;
                    continue;
                } else {
                    v_val_1230_ = leanh::lean_ctor_get(v___x_1229_, 0);
                    leanh::lean_inc(v_val_1230_);
                    leanh::lean_dec_ref_known(v___x_1229_, 1);
                    match leanh::lean_obj_tag(v_val_1230_) {
                        0 => {
                            leanh::lean_dec_ref(v___x_1227_);
                            v_val_1231_ = leanh::lean_ctor_get(v_val_1230_, 0);
                            leanh::lean_inc_ref(v_val_1231_);
                            leanh::lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1232_ = leanh::lean_ctor_get(v_val_1231_, 0);
                            leanh::lean_inc_ref(v_toConstantVal_1232_);
                            leanh::lean_dec_ref(v_val_1231_);
                            v_type_1233_ = leanh::lean_ctor_get(v_toConstantVal_1232_, 2);
                            leanh::lean_inc_ref(v_type_1233_);
                            leanh::lean_dec_ref(v_toConstantVal_1232_);
                            leanh::lean_inc(v_c_1141_);
                            v___x_1234_ = l_Lean_NameSet_insert(v___x_1225_, v_c_1141_);
                            v___x_1235_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_1235_, 0, v___x_1224_);
                            leanh::lean_ctor_set(v___x_1235_, 1, v___x_1234_);
                            v___x_1236_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1233_, v_a_1142_, v___x_1235_);
                            v_snd_1237_ = leanh::lean_ctor_get(v___x_1236_, 1);
                            leanh::lean_inc(v_snd_1237_);
                            leanh::lean_dec_ref(v___x_1236_);
                            v___y_1212_ = v_snd_1237_;
                            state = 11;
                            continue;
                        }
                        4 => {
                            leanh::lean_dec_ref_known(v_val_1230_, 1);
                            leanh::lean_dec(v___x_1224_);
                            leanh::lean_dec_ref(v_extFind_x3f_1140_);
                            v___y_1207_ = v___x_1227_;
                            v_axioms_1208_ = v___x_1225_;
                            state = 10;
                            continue;
                        }
                        5 => {
                            leanh::lean_dec(v___x_1224_);
                            v_val_1238_ = leanh::lean_ctor_get(v_val_1230_, 0);
                            leanh::lean_inc_ref(v_val_1238_);
                            leanh::lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1239_ = leanh::lean_ctor_get(v_val_1238_, 0);
                            leanh::lean_inc_ref(v_toConstantVal_1239_);
                            v_ctors_1240_ = leanh::lean_ctor_get(v_val_1238_, 4);
                            leanh::lean_inc(v_ctors_1240_);
                            leanh::lean_dec_ref(v_val_1238_);
                            v_type_1241_ = leanh::lean_ctor_get(v_toConstantVal_1239_, 2);
                            leanh::lean_inc_ref(v_type_1241_);
                            leanh::lean_dec_ref(v_toConstantVal_1239_);
                            leanh::lean_inc_ref(v_extFind_x3f_1140_);
                            v___x_1242_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1241_, v_a_1142_, v___x_1227_);
                            v_snd_1243_ = leanh::lean_ctor_get(v___x_1242_, 1);
                            leanh::lean_inc(v_snd_1243_);
                            leanh::lean_dec_ref(v___x_1242_);
                            v___x_1244_ = l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(v_extFind_x3f_1140_, v_ctors_1240_, v_a_1142_, v_snd_1243_);
                            v_snd_1245_ = leanh::lean_ctor_get(v___x_1244_, 1);
                            leanh::lean_inc(v_snd_1245_);
                            leanh::lean_dec_ref(v___x_1244_);
                            v___y_1212_ = v_snd_1245_;
                            state = 11;
                            continue;
                        }
                        6 => {
                            leanh::lean_dec(v___x_1224_);
                            v_val_1246_ = leanh::lean_ctor_get(v_val_1230_, 0);
                            leanh::lean_inc_ref(v_val_1246_);
                            leanh::lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1247_ = leanh::lean_ctor_get(v_val_1246_, 0);
                            leanh::lean_inc_ref(v_toConstantVal_1247_);
                            leanh::lean_dec_ref(v_val_1246_);
                            v_type_1248_ = leanh::lean_ctor_get(v_toConstantVal_1247_, 2);
                            leanh::lean_inc_ref(v_type_1248_);
                            leanh::lean_dec_ref(v_toConstantVal_1247_);
                            v___x_1249_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1248_, v_a_1142_, v___x_1227_);
                            v_snd_1250_ = leanh::lean_ctor_get(v___x_1249_, 1);
                            leanh::lean_inc(v_snd_1250_);
                            leanh::lean_dec_ref(v___x_1249_);
                            v___y_1212_ = v_snd_1250_;
                            state = 11;
                            continue;
                        }
                        7 => {
                            leanh::lean_dec(v___x_1224_);
                            v_val_1251_ = leanh::lean_ctor_get(v_val_1230_, 0);
                            leanh::lean_inc_ref(v_val_1251_);
                            leanh::lean_dec_ref_known(v_val_1230_, 1);
                            v_toConstantVal_1252_ = leanh::lean_ctor_get(v_val_1251_, 0);
                            leanh::lean_inc_ref(v_toConstantVal_1252_);
                            leanh::lean_dec_ref(v_val_1251_);
                            v_type_1253_ = leanh::lean_ctor_get(v_toConstantVal_1252_, 2);
                            leanh::lean_inc_ref(v_type_1253_);
                            leanh::lean_dec_ref(v_toConstantVal_1252_);
                            v___x_1254_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1253_, v_a_1142_, v___x_1227_);
                            v_snd_1255_ = leanh::lean_ctor_get(v___x_1254_, 1);
                            leanh::lean_inc(v_snd_1255_);
                            leanh::lean_dec_ref(v___x_1254_);
                            v___y_1212_ = v_snd_1255_;
                            state = 11;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec(v___x_1224_);
                            v_val_1256_ = leanh::lean_ctor_get(v_val_1230_, 0);
                            leanh::lean_inc_ref(v_val_1256_);
                            leanh::lean_dec(v_val_1230_);
                            v_toConstantVal_1257_ = leanh::lean_ctor_get(v_val_1256_, 0);
                            leanh::lean_inc_ref(v_toConstantVal_1257_);
                            v_value_1258_ = leanh::lean_ctor_get(v_val_1256_, 1);
                            leanh::lean_inc_ref(v_value_1258_);
                            leanh::lean_dec_ref(v_val_1256_);
                            v_type_1259_ = leanh::lean_ctor_get(v_toConstantVal_1257_, 2);
                            leanh::lean_inc_ref(v_type_1259_);
                            leanh::lean_dec_ref(v_toConstantVal_1257_);
                            leanh::lean_inc_ref(v_extFind_x3f_1140_);
                            v___x_1260_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_type_1259_, v_a_1142_, v___x_1227_);
                            v_snd_1261_ = leanh::lean_ctor_get(v___x_1260_, 1);
                            leanh::lean_inc(v_snd_1261_);
                            leanh::lean_dec_ref(v___x_1260_);
                            v___x_1262_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(v_extFind_x3f_1140_, v_value_1258_, v_a_1142_, v_snd_1261_);
                            v_snd_1263_ = leanh::lean_ctor_get(v___x_1262_, 1);
                            leanh::lean_inc(v_snd_1263_);
                            leanh::lean_dec_ref(v___x_1262_);
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
    mut v_extFind_x3f_1266_: *mut leanh::LeanObject,
    mut v_as_1267_: *mut leanh::LeanObject,
    mut v___y_1268_: *mut leanh::LeanObject,
    mut v___y_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_1267_) == 0 {
                    leanh::lean_dec_ref(v_extFind_x3f_1266_);
                    v___x_1270_ = leanh::lean_box(0);
                    v___x_1271_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
                    leanh::lean_ctor_set(v___x_1271_, 1, v___y_1269_);
                    return v___x_1271_;
                } else {
                    v_head_1272_ = leanh::lean_ctor_get(v_as_1267_, 0);
                    leanh::lean_inc(v_head_1272_);
                    v_tail_1273_ = leanh::lean_ctor_get(v_as_1267_, 1);
                    leanh::lean_inc(v_tail_1273_);
                    leanh::lean_dec_ref_known(v_as_1267_, 2);
                    leanh::lean_inc_ref(v_extFind_x3f_1266_);
                    v___x_1274_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
                        v_extFind_x3f_1266_,
                        v_head_1272_,
                        v___y_1268_,
                        v___y_1269_,
                    );
                    v_snd_1275_ = leanh::lean_ctor_get(v___x_1274_, 1);
                    leanh::lean_inc(v_snd_1275_);
                    leanh::lean_dec_ref(v___x_1274_);
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
    mut v_extFind_x3f_1277_: *mut leanh::LeanObject,
    mut v_as_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
    mut v___y_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_List_forM___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__3(v_extFind_x3f_1277_, v_as_1278_, v___y_1279_, v___y_1280_);
    leanh::lean_dec_ref(v___y_1279_);
    return v_res_1281_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0___boxed(
    mut v_extFind_x3f_1282_: *mut leanh::LeanObject,
    mut v_as_1283_: *mut leanh::LeanObject,
    mut v_i_1284_: *mut leanh::LeanObject,
    mut v_stop_1285_: *mut leanh::LeanObject,
    mut v_b_1286_: *mut leanh::LeanObject,
    mut v___y_1287_: *mut leanh::LeanObject,
    mut v___y_1288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1289_: usize = 0;
    let mut v_stop_boxed_1290_: usize = 0;
    let mut v_res_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1289_ = leanh::lean_unbox_usize(v_i_1284_);
    leanh::lean_dec(v_i_1284_);
    v_stop_boxed_1290_ = leanh::lean_unbox_usize(v_stop_1285_);
    leanh::lean_dec(v_stop_1285_);
    v_res_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__0(v_extFind_x3f_1282_, v_as_1283_, v_i_boxed_1289_, v_stop_boxed_1290_, v_b_1286_, v___y_1287_, v___y_1288_);
    leanh::lean_dec_ref(v___y_1287_);
    leanh::lean_dec_ref(v_as_1283_);
    return v_res_1291_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0___boxed(
    mut v_extFind_x3f_1292_: *mut leanh::LeanObject,
    mut v_e_1293_: *mut leanh::LeanObject,
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___lam__0(
        v_extFind_x3f_1292_,
        v_e_1293_,
        v___y_1294_,
        v___y_1295_,
    );
    leanh::lean_dec_ref(v___y_1294_);
    return v_res_1296_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___boxed(
    mut v_extFind_x3f_1297_: *mut leanh::LeanObject,
    mut v_c_1298_: *mut leanh::LeanObject,
    mut v_a_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
        v_extFind_x3f_1297_,
        v_c_1298_,
        v_a_1299_,
        v_a_1300_,
    );
    leanh::lean_dec_ref(v_a_1299_);
    return v_res_1301_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1(
    mut v_init_1302_: *mut leanh::LeanObject,
    mut v_t_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__1_spec__1(v_init_1302_, v_t_1303_);
    return v___x_1304_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(
    mut v_n_1305_: *mut leanh::LeanObject,
    mut v_as_1306_: *mut leanh::LeanObject,
    mut v_lo_1307_: *mut leanh::LeanObject,
    mut v_hi_1308_: *mut leanh::LeanObject,
    mut v_w_1309_: *mut leanh::LeanObject,
    mut v_hlo_1310_: *mut leanh::LeanObject,
    mut v_hhi_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___redArg(v_n_1305_, v_as_1306_, v_lo_1307_, v_hi_1308_);
    return v___x_1312_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2___boxed(
    mut v_n_1313_: *mut leanh::LeanObject,
    mut v_as_1314_: *mut leanh::LeanObject,
    mut v_lo_1315_: *mut leanh::LeanObject,
    mut v_hi_1316_: *mut leanh::LeanObject,
    mut v_w_1317_: *mut leanh::LeanObject,
    mut v_hlo_1318_: *mut leanh::LeanObject,
    mut v_hhi_1319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1320_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2(v_n_1313_, v_as_1314_, v_lo_1315_, v_hi_1316_, v_w_1317_, v_hlo_1318_, v_hhi_1319_);
    leanh::lean_dec(v_hi_1316_);
    leanh::lean_dec(v_n_1313_);
    return v_res_1320_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(
    mut v_n_1321_: *mut leanh::LeanObject,
    mut v_lo_1322_: *mut leanh::LeanObject,
    mut v_hi_1323_: *mut leanh::LeanObject,
    mut v_hhi_1324_: *mut leanh::LeanObject,
    mut v_pivot_1325_: *mut leanh::LeanObject,
    mut v_as_1326_: *mut leanh::LeanObject,
    mut v_i_1327_: *mut leanh::LeanObject,
    mut v_k_1328_: *mut leanh::LeanObject,
    mut v_ilo_1329_: *mut leanh::LeanObject,
    mut v_ik_1330_: *mut leanh::LeanObject,
    mut v_w_1331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___redArg(v_hi_1323_, v_pivot_1325_, v_as_1326_, v_i_1327_, v_k_1328_);
    return v___x_1332_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3___boxed(
    mut v_n_1333_: *mut leanh::LeanObject,
    mut v_lo_1334_: *mut leanh::LeanObject,
    mut v_hi_1335_: *mut leanh::LeanObject,
    mut v_hhi_1336_: *mut leanh::LeanObject,
    mut v_pivot_1337_: *mut leanh::LeanObject,
    mut v_as_1338_: *mut leanh::LeanObject,
    mut v_i_1339_: *mut leanh::LeanObject,
    mut v_k_1340_: *mut leanh::LeanObject,
    mut v_ilo_1341_: *mut leanh::LeanObject,
    mut v_ik_1342_: *mut leanh::LeanObject,
    mut v_w_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect_spec__2_spec__3(v_n_1333_, v_lo_1334_, v_hi_1335_, v_hhi_1336_, v_pivot_1337_, v_as_1338_, v_i_1339_, v_k_1340_, v_ilo_1341_, v_ik_1342_, v_w_1343_);
    leanh::lean_dec(v_pivot_1337_);
    leanh::lean_dec(v_hi_1335_);
    leanh::lean_dec(v_lo_1334_);
    leanh::lean_dec(v_n_1333_);
    return v_res_1344_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1352_ = l_Array_instInhabited(leanh::lean_box(0));
    return v___x_1352_;
}
pub unsafe fn l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(
    mut v_msg_1353_: *mut leanh::LeanObject,
    mut v___y_1354_: *mut leanh::LeanObject,
    mut v___y_1355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017__overap_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1356_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__0;
    v___f_1357_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__1;
    v___f_1358_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__2;
    v___f_1359_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__3;
    v___f_1360_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__4;
    v___f_1361_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__5;
    v___f_1362_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__6;
    v___x_1363_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1363_, 0, v___f_1356_);
    leanh::lean_ctor_set(v___x_1363_, 1, v___f_1357_);
    v___x_1364_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1364_, 0, v___x_1363_);
    leanh::lean_ctor_set(v___x_1364_, 1, v___f_1358_);
    leanh::lean_ctor_set(v___x_1364_, 2, v___f_1359_);
    leanh::lean_ctor_set(v___x_1364_, 3, v___f_1360_);
    leanh::lean_ctor_set(v___x_1364_, 4, v___f_1361_);
    v___x_1365_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1365_, 0, v___x_1364_);
    leanh::lean_ctor_set(v___x_1365_, 1, v___f_1362_);
    leanh::lean_inc_ref_n(v___x_1365_, 6);
    v___f_1366_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1366_, 0, v___x_1365_);
    v___f_1367_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1367_, 0, v___x_1365_);
    v___f_1368_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1368_, 0, v___x_1365_);
    v___f_1369_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1369_, 0, v___x_1365_);
    v___x_1370_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1370_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1370_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1370_, 2, v___x_1365_);
    v___x_1371_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1371_, 0, v___x_1370_);
    leanh::lean_ctor_set(v___x_1371_, 1, v___f_1366_);
    v___x_1372_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_1372_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1372_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1372_, 2, v___x_1365_);
    v___x_1373_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_1373_, 0, v___x_1371_);
    leanh::lean_ctor_set(v___x_1373_, 1, v___x_1372_);
    leanh::lean_ctor_set(v___x_1373_, 2, v___f_1367_);
    leanh::lean_ctor_set(v___x_1373_, 3, v___f_1368_);
    leanh::lean_ctor_set(v___x_1373_, 4, v___f_1369_);
    v___x_1374_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_1374_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1374_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1374_, 2, v___x_1365_);
    v___x_1375_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1375_, 0, v___x_1373_);
    leanh::lean_ctor_set(v___x_1375_, 1, v___x_1374_);
    v___x_1376_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7_once), _init_l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___closed__7);
    v___x_1377_ = l_instInhabitedOfMonad___redArg(v___x_1375_, v___x_1376_);
    v___f_1378_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1378_, 0, v___x_1377_);
    v___x_1017__overap_1379_ = lean_panic_fn_borrowed(v___f_1378_, v_msg_1353_);
    leanh::lean_dec_ref(v___f_1378_);
    leanh::lean_inc_ref(v___y_1354_);
    v___x_1380_ = leanh::lean_apply_2(v___x_1017__overap_1379_, v___y_1354_, v___y_1355_);
    return v___x_1380_;
}
pub unsafe fn l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0___boxed(
    mut v_msg_1381_: *mut leanh::LeanObject,
    mut v___y_1382_: *mut leanh::LeanObject,
    mut v___y_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_panic___at___00__private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet_spec__0(v_msg_1381_, v___y_1382_, v___y_1383_);
    leanh::lean_dec_ref(v___y_1382_);
    return v_res_1384_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(
    mut v_extFind_x3f_1389_: *mut leanh::LeanObject,
    mut v_c_1390_: *mut leanh::LeanObject,
    mut v_a_1391_: *mut leanh::LeanObject,
    mut v_a_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1397_: u8 = 0;
    let mut v_seen_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: u8 = 0;
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1416_: u8 = 0;
    let mut v_unused_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_c_1390_);
                v___x_1393_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect(
                    v_extFind_x3f_1389_,
                    v_c_1390_,
                    v_a_1391_,
                    v_a_1392_,
                );
                v_snd_1394_ = leanh::lean_ctor_get(v___x_1393_, 1);
                v_isSharedCheck_1416_ = (!leanh::lean_is_exclusive(v___x_1393_)) as u8;
                if v_isSharedCheck_1416_ == 0 {
                    v_unused_1417_ = leanh::lean_ctor_get(v___x_1393_, 0);
                    leanh::lean_dec(v_unused_1417_);
                    v___x_1396_ = v___x_1393_;
                    v_isShared_1397_ = v_isSharedCheck_1416_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1394_);
                    leanh::lean_dec(v___x_1393_);
                    v___x_1396_ = leanh::lean_box(0);
                    v_isShared_1397_ = v_isSharedCheck_1416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_seen_1398_ = leanh::lean_ctor_get(v_snd_1394_, 0);
                v___x_1399_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_seen_1398_, v_c_1390_);
                if leanh::lean_obj_tag(v___x_1399_) == 1 {
                    leanh::lean_dec(v_c_1390_);
                    v_val_1400_ = leanh::lean_ctor_get(v___x_1399_, 0);
                    leanh::lean_inc(v_val_1400_);
                    leanh::lean_dec_ref_known(v___x_1399_, 1);
                    if v_isShared_1397_ == 0 {
                        leanh::lean_ctor_set(v___x_1396_, 0, v_val_1400_);
                        v___x_1402_ = v___x_1396_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1403_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_val_1400_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_snd_1394_);
                        v___x_1402_ = v_reuseFailAlloc_1403_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1399_);
                    leanh::lean_del_object(v___x_1396_);
                    v___x_1404_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__0;
                    v___x_1405_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__1;
                    v___x_1406_ = leanh::lean_unsigned_to_nat(81);
                    v___x_1407_ = leanh::lean_unsigned_to_nat(41);
                    v___x_1408_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__2;
                    v___x_1409_ = 1;
                    v___x_1410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_c_1390_,
                        v___x_1409_,
                    );
                    v___x_1411_ = lean_string_append(v___x_1408_, v___x_1410_);
                    leanh::lean_dec_ref(v___x_1410_);
                    v___x_1412_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___closed__3;
                    v___x_1413_ = lean_string_append(v___x_1411_, v___x_1412_);
                    v___x_1414_ = l_mkPanicMessageWithDecl(
                        v___x_1404_,
                        v___x_1405_,
                        v___x_1406_,
                        v___x_1407_,
                        v___x_1413_,
                    );
                    leanh::lean_dec_ref(v___x_1413_);
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
    mut v_extFind_x3f_1418_: *mut leanh::LeanObject,
    mut v_c_1419_: *mut leanh::LeanObject,
    mut v_a_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1422_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(
        v_extFind_x3f_1418_,
        v_c_1419_,
        v_a_1420_,
        v_a_1421_,
    );
    leanh::lean_dec_ref(v_a_1420_);
    return v_res_1422_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(
    mut v_a_1426_: *mut leanh::LeanObject,
    mut v_b_1427_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: u8 = 0;
    v_fst_1428_ = leanh::lean_ctor_get(v_a_1426_, 0);
    v_fst_1429_ = leanh::lean_ctor_get(v_b_1427_, 0);
    v___x_1430_ = l_Lean_Name_quickLt(v_fst_1428_, v_fst_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0___boxed(
    mut v_a_1431_: *mut leanh::LeanObject,
    mut v_b_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1433_: u8 = 0;
    let mut v_r_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1433_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_1431_, v_b_1432_);
    leanh::lean_dec_ref(v_b_1432_);
    leanh::lean_dec_ref(v_a_1431_);
    v_r_1434_ = leanh::lean_box((v_res_1433_) as usize);
    return v_r_1434_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(
    mut v_as_1435_: *mut leanh::LeanObject,
    mut v_k_1436_: *mut leanh::LeanObject,
    mut v_x_1437_: *mut leanh::LeanObject,
    mut v_x_1438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: u8 = 0;
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1439_ = lean_nat_add(v_x_1437_, v_x_1438_);
                v___x_1440_ = leanh::lean_unsigned_to_nat(1);
                v_m_1441_ = lean_nat_shiftr(v___x_1439_, v___x_1440_);
                leanh::lean_dec(v___x_1439_);
                v_a_1442_ = lean_array_fget_borrowed(v_as_1435_, v_m_1441_);
                v___x_1443_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_a_1442_, v_k_1436_);
                if v___x_1443_ == 0 {
                    leanh::lean_dec(v_x_1438_);
                    v___x_1444_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v_k_1436_, v_a_1442_);
                    if v___x_1444_ == 0 {
                        leanh::lean_dec(v_m_1441_);
                        leanh::lean_dec(v_x_1437_);
                        leanh::lean_inc(v_a_1442_);
                        v___x_1445_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1445_, 0, v_a_1442_);
                        return v___x_1445_;
                    } else {
                        v___x_1446_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1447_ = lean_nat_dec_eq(v_m_1441_, v___x_1446_);
                        if v___x_1447_ == 0 {
                            v___x_1448_ = lean_nat_sub(v_m_1441_, v___x_1440_);
                            leanh::lean_dec(v_m_1441_);
                            v___x_1449_ = lean_nat_dec_lt(v___x_1448_, v_x_1437_);
                            if v___x_1449_ == 0 {
                                v_x_1438_ = v___x_1448_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1448_);
                                leanh::lean_dec(v_x_1437_);
                                v___x_1451_ = leanh::lean_box(0);
                                return v___x_1451_;
                            }
                        } else {
                            leanh::lean_dec(v_m_1441_);
                            leanh::lean_dec(v_x_1437_);
                            v___x_1452_ = leanh::lean_box(0);
                            return v___x_1452_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_x_1437_);
                    v___x_1453_ = lean_nat_add(v_m_1441_, v___x_1440_);
                    leanh::lean_dec(v_m_1441_);
                    v___x_1454_ = lean_nat_dec_le(v___x_1453_, v_x_1438_);
                    if v___x_1454_ == 0 {
                        leanh::lean_dec(v___x_1453_);
                        leanh::lean_dec(v_x_1438_);
                        v___x_1455_ = leanh::lean_box(0);
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
    mut v_as_1457_: *mut leanh::LeanObject,
    mut v_k_1458_: *mut leanh::LeanObject,
    mut v_x_1459_: *mut leanh::LeanObject,
    mut v_x_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1461_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v_as_1457_, v_k_1458_, v_x_1459_, v_x_1460_);
    leanh::lean_dec_ref(v_k_1458_);
    leanh::lean_dec_ref(v_as_1457_);
    return v_res_1461_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(
    mut v_s_1462_: *mut leanh::LeanObject,
    mut v_env_1463_: *mut leanh::LeanObject,
    mut v_c_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v_snd_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1465_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1463_, v_c_1464_);
                if leanh::lean_obj_tag(v___x_1465_) == 0 {
                    leanh::lean_dec(v_c_1464_);
                    v___x_1466_ = leanh::lean_box(0);
                    return v___x_1466_;
                } else {
                    v_val_1467_ = leanh::lean_ctor_get(v___x_1465_, 0);
                    leanh::lean_inc(v_val_1467_);
                    leanh::lean_dec_ref_known(v___x_1465_, 1);
                    v___x_1468_ = lean_array_get_size(v_s_1462_);
                    v___x_1469_ = lean_nat_dec_lt(v_val_1467_, v___x_1468_);
                    if v___x_1469_ == 0 {
                        leanh::lean_dec(v_val_1467_);
                        leanh::lean_dec(v_c_1464_);
                        v___x_1470_ = leanh::lean_box(0);
                        return v___x_1470_;
                    } else {
                        v___x_1471_ = lean_array_fget_borrowed(v_s_1462_, v_val_1467_);
                        leanh::lean_dec(v_val_1467_);
                        v___x_1472_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1473_ = lean_array_get_size(v___x_1471_);
                        v___x_1474_ = lean_nat_dec_lt(v___x_1472_, v___x_1473_);
                        if v___x_1474_ == 0 {
                            leanh::lean_dec(v_c_1464_);
                            v___x_1475_ = leanh::lean_box(0);
                            return v___x_1475_;
                        } else {
                            v___x_1476_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1477_ = lean_nat_sub(v___x_1473_, v___x_1476_);
                            v___x_1478_ = lean_nat_dec_le(v___x_1472_, v___x_1477_);
                            if v___x_1478_ == 0 {
                                leanh::lean_dec(v___x_1477_);
                                leanh::lean_dec(v_c_1464_);
                                v___x_1479_ = leanh::lean_box(0);
                                return v___x_1479_;
                            } else {
                                v___x_1480_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collect___closed__0;
                                v___x_1481_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1481_, 0, v_c_1464_);
                                leanh::lean_ctor_set(v___x_1481_, 1, v___x_1480_);
                                v___x_1482_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v___x_1471_, v___x_1481_, v___x_1472_, v___x_1477_);
                                leanh::lean_dec_ref_known(v___x_1481_, 2);
                                if leanh::lean_obj_tag(v___x_1482_) == 0 {
                                    v___x_1483_ = leanh::lean_box(0);
                                    return v___x_1483_;
                                } else {
                                    v_val_1484_ = leanh::lean_ctor_get(v___x_1482_, 0);
                                    v_isSharedCheck_1492_ =
                                        (!leanh::lean_is_exclusive(v___x_1482_)) as u8;
                                    if v_isSharedCheck_1492_ == 0 {
                                        v___x_1486_ = v___x_1482_;
                                        v_isShared_1487_ = v_isSharedCheck_1492_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_val_1484_);
                                        leanh::lean_dec(v___x_1482_);
                                        v___x_1486_ = leanh::lean_box(0);
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
                v_snd_1488_ = leanh::lean_ctor_get(v_val_1484_, 1);
                leanh::lean_inc(v_snd_1488_);
                leanh::lean_dec(v_val_1484_);
                if v_isShared_1487_ == 0 {
                    leanh::lean_ctor_set(v___x_1486_, 0, v_snd_1488_);
                    v___x_1490_ = v___x_1486_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_snd_1488_);
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
    mut v_s_1493_: *mut leanh::LeanObject,
    mut v_env_1494_: *mut leanh::LeanObject,
    mut v_c_1495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1496_ = l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f(
        v_s_1493_,
        v_env_1494_,
        v_c_1495_,
    );
    leanh::lean_dec_ref(v_env_1494_);
    leanh::lean_dec_ref(v_s_1493_);
    return v_res_1496_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(
    mut v_as_1497_: *mut leanh::LeanObject,
    mut v_k_1498_: *mut leanh::LeanObject,
    mut v_x_1499_: *mut leanh::LeanObject,
    mut v_x_1500_: *mut leanh::LeanObject,
    mut v_x_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg(v_as_1497_, v_k_1498_, v_x_1499_, v_x_1500_);
    return v___x_1502_;
}
pub unsafe fn l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___boxed(
    mut v_as_1503_: *mut leanh::LeanObject,
    mut v_k_1504_: *mut leanh::LeanObject,
    mut v_x_1505_: *mut leanh::LeanObject,
    mut v_x_1506_: *mut leanh::LeanObject,
    mut v_x_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0(v_as_1503_, v_k_1504_, v_x_1505_, v_x_1506_, v_x_1507_);
    leanh::lean_dec_ref(v_k_1504_);
    leanh::lean_dec_ref(v_as_1503_);
    return v_res_1508_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_x_1511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1512_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_;
    return v___x_1512_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_x_1513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1514_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__0_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_x_1513_);
    leanh::lean_dec_ref(v_x_1513_);
    return v_res_1514_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_x_1515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1516_ = leanh::lean_box(0);
    return v___x_1516_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_x_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1518_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_x_1517_);
    leanh::lean_dec_ref(v_x_1517_);
    return v_res_1518_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_s_1519_: *mut leanh::LeanObject,
    mut v_x_1520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_s_1519_);
    return v_s_1519_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_s_1521_: *mut leanh::LeanObject,
    mut v_x_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1523_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__2_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_s_1521_, v_x_1522_);
    leanh::lean_dec_ref(v_x_1522_);
    leanh::lean_dec_ref(v_s_1521_);
    return v_res_1523_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_importedEntries_1524_: *mut leanh::LeanObject,
    mut v___y_1525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1527_, 0, v_importedEntries_1524_);
    return v___x_1527_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_importedEntries_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
    mut v___y_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1531_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__3_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_importedEntries_1528_, v___y_1529_);
    leanh::lean_dec_ref(v___y_1529_);
    return v_res_1531_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v_exportedEnv_1532_: *mut leanh::LeanObject,
    mut v___x_1533_: u8,
    mut v_names_1534_: *mut leanh::LeanObject,
    mut v_name_1535_: *mut leanh::LeanObject,
    mut v_x_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_name_1535_);
    v___x_1537_ = l_Lean_Environment_find_x3f(v_exportedEnv_1532_, v_name_1535_, v___x_1533_);
    if leanh::lean_obj_tag(v___x_1537_) == 0 {
        leanh::lean_dec(v_name_1535_);
        return v_names_1534_;
    } else {
        let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_1537_, 1);
        v___x_1538_ = lean_array_push(v_names_1534_, v_name_1535_);
        return v___x_1538_;
    }
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_exportedEnv_1539_: *mut leanh::LeanObject,
    mut v___x_1540_: *mut leanh::LeanObject,
    mut v_names_1541_: *mut leanh::LeanObject,
    mut v_name_1542_: *mut leanh::LeanObject,
    mut v_x_1543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1738__boxed_1544_: u8 = 0;
    let mut v_res_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1738__boxed_1544_ = (leanh::lean_unbox(v___x_1540_) as u8);
    v_res_1545_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v_exportedEnv_1539_, v___x_1738__boxed_1544_, v_names_1541_, v_name_1542_, v_x_1543_);
    leanh::lean_dec_ref(v_x_1543_);
    return v_res_1545_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__1(
    mut v_s_1546_: *mut leanh::LeanObject,
    mut v_sz_1547_: usize,
    mut v_i_1548_: usize,
    mut v_bs_1549_: *mut leanh::LeanObject,
    mut v___y_1550_: *mut leanh::LeanObject,
    mut v___y_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1561_: u8 = 0;
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: usize = 0;
    let mut v___x_1567_: usize = 0;
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1571_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1552_ = lean_usize_dec_lt(v_i_1548_, v_sz_1547_);
                if v___x_1552_ == 0 {
                    leanh::lean_dec_ref(v_s_1546_);
                    v___x_1553_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1553_, 0, v_bs_1549_);
                    leanh::lean_ctor_set(v___x_1553_, 1, v___y_1551_);
                    return v___x_1553_;
                } else {
                    v_v_1554_ = lean_array_uget(v_bs_1549_, v_i_1548_);
                    leanh::lean_inc_ref(v_s_1546_);
                    v___x_1555_ = leanh::lean_alloc_closure(l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed as *mut core::ffi::c_void, 3, 1);
                    leanh::lean_closure_set(v___x_1555_, 0, v_s_1546_);
                    leanh::lean_inc(v_v_1554_);
                    v___x_1556_ =
                        l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet(
                            v___x_1555_,
                            v_v_1554_,
                            v___y_1550_,
                            v___y_1551_,
                        );
                    v_fst_1557_ = leanh::lean_ctor_get(v___x_1556_, 0);
                    v_snd_1558_ = leanh::lean_ctor_get(v___x_1556_, 1);
                    v_isSharedCheck_1571_ = (!leanh::lean_is_exclusive(v___x_1556_)) as u8;
                    if v_isSharedCheck_1571_ == 0 {
                        v___x_1560_ = v___x_1556_;
                        v_isShared_1561_ = v_isSharedCheck_1571_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1558_);
                        leanh::lean_inc(v_fst_1557_);
                        leanh::lean_dec(v___x_1556_);
                        v___x_1560_ = leanh::lean_box(0);
                        v_isShared_1561_ = v_isSharedCheck_1571_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1562_ = leanh::lean_unsigned_to_nat(0);
                v_bs_x27_1563_ = lean_array_uset(v_bs_1549_, v_i_1548_, v___x_1562_);
                if v_isShared_1561_ == 0 {
                    leanh::lean_ctor_set(v___x_1560_, 1, v_fst_1557_);
                    leanh::lean_ctor_set(v___x_1560_, 0, v_v_1554_);
                    v___x_1565_ = v___x_1560_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1570_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_v_1554_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_fst_1557_);
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
    mut v_s_1572_: *mut leanh::LeanObject,
    mut v_sz_1573_: *mut leanh::LeanObject,
    mut v_i_1574_: *mut leanh::LeanObject,
    mut v_bs_1575_: *mut leanh::LeanObject,
    mut v___y_1576_: *mut leanh::LeanObject,
    mut v___y_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1578_: usize = 0;
    let mut v_i_boxed_1579_: usize = 0;
    let mut v_res_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1578_ = leanh::lean_unbox_usize(v_sz_1573_);
    leanh::lean_dec(v_sz_1573_);
    v_i_boxed_1579_ = leanh::lean_unbox_usize(v_i_1574_);
    leanh::lean_dec(v_i_1574_);
    v_res_1580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__1(v_s_1572_, v_sz_boxed_1578_, v_i_boxed_1579_, v_bs_1575_, v___y_1576_, v___y_1577_);
    leanh::lean_dec_ref(v___y_1576_);
    return v_res_1580_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_f_1581_: *mut leanh::LeanObject,
    mut v_keys_1582_: *mut leanh::LeanObject,
    mut v_vals_1583_: *mut leanh::LeanObject,
    mut v_i_1584_: *mut leanh::LeanObject,
    mut v_acc_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: u8 = 0;
    let mut v_k_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1586_ = lean_array_get_size(v_keys_1582_);
                v___x_1587_ = lean_nat_dec_lt(v_i_1584_, v___x_1586_);
                if v___x_1587_ == 0 {
                    leanh::lean_dec(v_i_1584_);
                    leanh::lean_dec(v_f_1581_);
                    return v_acc_1585_;
                } else {
                    v_k_1588_ = lean_array_fget_borrowed(v_keys_1582_, v_i_1584_);
                    v_v_1589_ = lean_array_fget_borrowed(v_vals_1583_, v_i_1584_);
                    leanh::lean_inc(v_f_1581_);
                    leanh::lean_inc(v_v_1589_);
                    leanh::lean_inc(v_k_1588_);
                    v___x_1590_ =
                        leanh::lean_apply_3(v_f_1581_, v_acc_1585_, v_k_1588_, v_v_1589_);
                    v___x_1591_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1592_ = lean_nat_add(v_i_1584_, v___x_1591_);
                    leanh::lean_dec(v_i_1584_);
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
    mut v_f_1594_: *mut leanh::LeanObject,
    mut v_keys_1595_: *mut leanh::LeanObject,
    mut v_vals_1596_: *mut leanh::LeanObject,
    mut v_i_1597_: *mut leanh::LeanObject,
    mut v_acc_1598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1599_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_1594_, v_keys_1595_, v_vals_1596_, v_i_1597_, v_acc_1598_);
    leanh::lean_dec_ref(v_vals_1596_);
    leanh::lean_dec_ref(v_keys_1595_);
    return v_res_1599_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_f_1600_: *mut leanh::LeanObject,
    mut v_x_1601_: *mut leanh::LeanObject,
    mut v_x_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1601_) == 0 {
        let mut v_es_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1606_: u8 = 0;
        v_es_1603_ = leanh::lean_ctor_get(v_x_1601_, 0);
        v___x_1604_ = leanh::lean_unsigned_to_nat(0);
        v___x_1605_ = lean_array_get_size(v_es_1603_);
        v___x_1606_ = lean_nat_dec_lt(v___x_1604_, v___x_1605_);
        if v___x_1606_ == 0 {
            leanh::lean_dec(v_f_1600_);
            return v_x_1602_;
        } else {
            let mut v___x_1607_: u8 = 0;
            v___x_1607_ = lean_nat_dec_le(v___x_1605_, v___x_1605_);
            if v___x_1607_ == 0 {
                if v___x_1606_ == 0 {
                    leanh::lean_dec(v_f_1600_);
                    return v_x_1602_;
                } else {
                    let mut v___x_1608_: usize = 0;
                    let mut v___x_1609_: usize = 0;
                    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1608_ = 0usize;
                    v___x_1609_ = lean_usize_of_nat(v___x_1605_);
                    v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1600_, v_es_1603_, v___x_1608_, v___x_1609_, v_x_1602_);
                    return v___x_1610_;
                }
            } else {
                let mut v___x_1611_: usize = 0;
                let mut v___x_1612_: usize = 0;
                let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1611_ = 0usize;
                v___x_1612_ = lean_usize_of_nat(v___x_1605_);
                v___x_1613_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1600_, v_es_1603_, v___x_1611_, v___x_1612_, v_x_1602_);
                return v___x_1613_;
            }
        }
    } else {
        let mut v_ks_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ks_1614_ = leanh::lean_ctor_get(v_x_1601_, 0);
        v_vs_1615_ = leanh::lean_ctor_get(v_x_1601_, 1);
        v___x_1616_ = leanh::lean_unsigned_to_nat(0);
        v___x_1617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_1600_, v_ks_1614_, v_vs_1615_, v___x_1616_, v_x_1602_);
        return v___x_1617_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_f_1618_: *mut leanh::LeanObject,
    mut v_as_1619_: *mut leanh::LeanObject,
    mut v_i_1620_: usize,
    mut v_stop_1621_: usize,
    mut v_b_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: usize = 0;
    let mut v___x_1626_: usize = 0;
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1628_ = lean_usize_dec_eq(v_i_1620_, v_stop_1621_);
                if v___x_1628_ == 0 {
                    v___x_1629_ = lean_array_uget_borrowed(v_as_1619_, v_i_1620_);
                    match leanh::lean_obj_tag(v___x_1629_) {
                        0 => {
                            v_key_1630_ = leanh::lean_ctor_get(v___x_1629_, 0);
                            v_val_1631_ = leanh::lean_ctor_get(v___x_1629_, 1);
                            leanh::lean_inc(v_f_1618_);
                            leanh::lean_inc(v_val_1631_);
                            leanh::lean_inc(v_key_1630_);
                            v___x_1632_ = leanh::lean_apply_3(
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
                            v_node_1633_ = leanh::lean_ctor_get(v___x_1629_, 0);
                            leanh::lean_inc(v_f_1618_);
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
                    leanh::lean_dec(v_f_1618_);
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
    mut v_f_1635_: *mut leanh::LeanObject,
    mut v_as_1636_: *mut leanh::LeanObject,
    mut v_i_1637_: *mut leanh::LeanObject,
    mut v_stop_1638_: *mut leanh::LeanObject,
    mut v_b_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1640_: usize = 0;
    let mut v_stop_boxed_1641_: usize = 0;
    let mut v_res_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1640_ = leanh::lean_unbox_usize(v_i_1637_);
    leanh::lean_dec(v_i_1637_);
    v_stop_boxed_1641_ = leanh::lean_unbox_usize(v_stop_1638_);
    leanh::lean_dec(v_stop_1638_);
    v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1635_, v_as_1636_, v_i_boxed_1640_, v_stop_boxed_1641_, v_b_1639_);
    leanh::lean_dec_ref(v_as_1636_);
    return v_res_1642_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_1643_: *mut leanh::LeanObject,
    mut v_x_1644_: *mut leanh::LeanObject,
    mut v_x_1645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1646_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1643_, v_x_1644_, v_x_1645_);
    leanh::lean_dec_ref(v_x_1644_);
    return v_res_1646_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg___lam__0(
    mut v_f_1647_: *mut leanh::LeanObject,
    mut v_x1_1648_: *mut leanh::LeanObject,
    mut v_x2_1649_: *mut leanh::LeanObject,
    mut v_x3_1650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = leanh::lean_apply_3(v_f_1647_, v_x1_1648_, v_x2_1649_, v_x3_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(
    mut v_map_1652_: *mut leanh::LeanObject,
    mut v_f_1653_: *mut leanh::LeanObject,
    mut v_init_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1655_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_1655_, 0, v_f_1653_);
    v___x_1656_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_1655_, v_map_1652_, v_init_1654_);
    return v___x_1656_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_map_1657_: *mut leanh::LeanObject,
    mut v_f_1658_: *mut leanh::LeanObject,
    mut v_init_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1660_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(v_map_1657_, v_f_1658_, v_init_1659_);
    leanh::lean_dec_ref(v_map_1657_);
    return v_res_1660_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(
    mut v_hi_1661_: *mut leanh::LeanObject,
    mut v_pivot_1662_: *mut leanh::LeanObject,
    mut v_as_1663_: *mut leanh::LeanObject,
    mut v_i_1664_: *mut leanh::LeanObject,
    mut v_k_1665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1666_ = lean_nat_dec_lt(v_k_1665_, v_hi_1661_);
                if v___x_1666_ == 0 {
                    leanh::lean_dec(v_k_1665_);
                    v___x_1667_ = lean_array_fswap(v_as_1663_, v_i_1664_, v_hi_1661_);
                    v___x_1668_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1668_, 0, v_i_1664_);
                    leanh::lean_ctor_set(v___x_1668_, 1, v___x_1667_);
                    return v___x_1668_;
                } else {
                    v___x_1669_ = lean_array_fget_borrowed(v_as_1663_, v_k_1665_);
                    v_fst_1670_ = leanh::lean_ctor_get(v___x_1669_, 0);
                    v_fst_1671_ = leanh::lean_ctor_get(v_pivot_1662_, 0);
                    v___x_1672_ = l_Lean_Name_quickLt(v_fst_1670_, v_fst_1671_);
                    if v___x_1672_ == 0 {
                        v___x_1673_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1674_ = lean_nat_add(v_k_1665_, v___x_1673_);
                        leanh::lean_dec(v_k_1665_);
                        v_k_1665_ = v___x_1674_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1676_ = lean_array_fswap(v_as_1663_, v_i_1664_, v_k_1665_);
                        v___x_1677_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1678_ = lean_nat_add(v_i_1664_, v___x_1677_);
                        leanh::lean_dec(v_i_1664_);
                        v___x_1679_ = lean_nat_add(v_k_1665_, v___x_1677_);
                        leanh::lean_dec(v_k_1665_);
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
    mut v_hi_1681_: *mut leanh::LeanObject,
    mut v_pivot_1682_: *mut leanh::LeanObject,
    mut v_as_1683_: *mut leanh::LeanObject,
    mut v_i_1684_: *mut leanh::LeanObject,
    mut v_k_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_1681_, v_pivot_1682_, v_as_1683_, v_i_1684_, v_k_1685_);
    leanh::lean_dec_ref(v_pivot_1682_);
    leanh::lean_dec(v_hi_1681_);
    return v_res_1686_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(
    mut v_n_1687_: *mut leanh::LeanObject,
    mut v_as_1688_: *mut leanh::LeanObject,
    mut v_lo_1689_: *mut leanh::LeanObject,
    mut v_hi_1690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: u8 = 0;
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: u8 = 0;
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1702_ = lean_nat_dec_lt(v_lo_1689_, v_hi_1690_);
                if v___x_1702_ == 0 {
                    leanh::lean_dec(v_lo_1689_);
                    return v_as_1688_;
                } else {
                    v___x_1703_ = lean_nat_add(v_lo_1689_, v_hi_1690_);
                    v___x_1704_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_1705_ = lean_nat_shiftr(v___x_1703_, v___x_1704_);
                    leanh::lean_dec(v___x_1703_);
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
                leanh::lean_inc_n(v_lo_1689_, 2);
                v___x_1694_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_1690_, v_pivot_1693_, v___y_1692_, v_lo_1689_, v_lo_1689_);
                leanh::lean_dec(v_pivot_1693_);
                v_fst_1695_ = leanh::lean_ctor_get(v___x_1694_, 0);
                leanh::lean_inc(v_fst_1695_);
                v_snd_1696_ = leanh::lean_ctor_get(v___x_1694_, 1);
                leanh::lean_inc(v_snd_1696_);
                leanh::lean_dec_ref(v___x_1694_);
                v___x_1697_ = lean_nat_dec_le(v_hi_1690_, v_fst_1695_);
                if v___x_1697_ == 0 {
                    v___x_1698_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v_n_1687_, v_snd_1696_, v_lo_1689_, v_fst_1695_);
                    v___x_1699_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1700_ = lean_nat_add(v_fst_1695_, v___x_1699_);
                    leanh::lean_dec(v_fst_1695_);
                    v_as_1688_ = v___x_1698_;
                    v_lo_1689_ = v___x_1700_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_1695_);
                    leanh::lean_dec(v_lo_1689_);
                    return v_snd_1696_;
                }
            }
            2 => {
                v___x_1708_ = lean_array_fget_borrowed(v___y_1707_, v_mid_1705_);
                v___x_1709_ = lean_array_fget_borrowed(v___y_1707_, v_hi_1690_);
                v___x_1710_ = l_Array_binSearchAux___at___00__private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f_spec__0___redArg___lam__0(v___x_1708_, v___x_1709_);
                if v___x_1710_ == 0 {
                    leanh::lean_dec(v_mid_1705_);
                    v___y_1692_ = v___y_1707_;
                    state = 1;
                    continue;
                } else {
                    v___x_1711_ = lean_array_fswap(v___y_1707_, v_mid_1705_, v_hi_1690_);
                    leanh::lean_dec(v_mid_1705_);
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
    mut v_n_1722_: *mut leanh::LeanObject,
    mut v_as_1723_: *mut leanh::LeanObject,
    mut v_lo_1724_: *mut leanh::LeanObject,
    mut v_hi_1725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v_n_1722_, v_as_1723_, v_lo_1724_, v_hi_1725_);
    leanh::lean_dec(v_hi_1725_);
    leanh::lean_dec(v_n_1722_);
    return v_res_1726_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(
    mut v___x_1729_: *mut leanh::LeanObject,
    mut v_env_1730_: *mut leanh::LeanObject,
    mut v_s_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checked_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_constants_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v_exportedEnv_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_privateEnv_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allNames_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1744_: usize = 0;
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: u8 = 0;
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_checked_1732_ = leanh::lean_ctor_get(v_env_1730_, 2);
                leanh::lean_inc_ref(v_checked_1732_);
                v___x_1733_ = lean_task_get_own(v_checked_1732_);
                v_constants_1734_ = leanh::lean_ctor_get(v___x_1733_, 0);
                leanh::lean_inc_ref(v_constants_1734_);
                leanh::lean_dec(v___x_1733_);
                v_map_u2082_1735_ = leanh::lean_ctor_get(v_constants_1734_, 1);
                leanh::lean_inc_ref(v_map_u2082_1735_);
                leanh::lean_dec_ref(v_constants_1734_);
                v___x_1736_ = 1;
                leanh::lean_inc_ref(v_env_1730_);
                v_exportedEnv_1737_ = l_Lean_Environment_setExporting(v_env_1730_, v___x_1736_);
                v___x_1738_ = 0;
                v___x_1739_ = leanh::lean_box((v___x_1738_) as usize);
                v___f_1740_ = leanh::lean_alloc_closure(l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__4_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 5, 2);
                leanh::lean_closure_set(v___f_1740_, 0, v_exportedEnv_1737_);
                leanh::lean_closure_set(v___f_1740_, 1, v___x_1739_);
                v_privateEnv_1741_ = l_Lean_Environment_setExporting(v_env_1730_, v___x_1738_);
                v___x_1742_ = lean_mk_empty_array_with_capacity(v___x_1729_);
                v_allNames_1743_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(v_map_u2082_1735_, v___f_1740_, v___x_1742_);
                leanh::lean_dec_ref(v_map_u2082_1735_);
                v_sz_1744_ = lean_array_size(v_allNames_1743_);
                v___x_1745_ = leanh::lean_box_usize(v_sz_1744_);
                v___x_1746_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__5___boxed__const__1_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_;
                v___x_1747_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__1___boxed as *mut core::ffi::c_void, 6, 4);
                leanh::lean_closure_set(v___x_1747_, 0, v_s_1731_);
                leanh::lean_closure_set(v___x_1747_, 1, v___x_1745_);
                leanh::lean_closure_set(v___x_1747_, 2, v___x_1746_);
                leanh::lean_closure_set(v___x_1747_, 3, v_allNames_1743_);
                v_entries_1748_ =
                    l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
                        v_privateEnv_1741_,
                        v___x_1747_,
                    );
                v___x_1749_ = lean_array_get_size(v_entries_1748_);
                v___x_1755_ = lean_nat_dec_eq(v___x_1749_, v___x_1729_);
                if v___x_1755_ == 0 {
                    v___x_1756_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1757_ = lean_nat_sub(v___x_1749_, v___x_1756_);
                    v___x_1761_ = lean_nat_dec_le(v___x_1729_, v___x_1757_);
                    if v___x_1761_ == 0 {
                        leanh::lean_dec(v___x_1729_);
                        leanh::lean_inc(v___x_1757_);
                        v___y_1759_ = v___x_1757_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1759_ = v___x_1729_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1729_);
                    leanh::lean_inc_n(v_entries_1748_, 2);
                    v___x_1762_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1762_, 0, v_entries_1748_);
                    leanh::lean_ctor_set(v___x_1762_, 1, v_entries_1748_);
                    leanh::lean_ctor_set(v___x_1762_, 2, v_entries_1748_);
                    return v___x_1762_;
                }
            }
            1 => {
                v___x_1753_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v___x_1749_, v_entries_1748_, v___y_1751_, v___y_1752_);
                leanh::lean_dec(v___y_1752_);
                leanh::lean_inc_ref_n(v___x_1753_, 2);
                v___x_1754_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1754_, 0, v___x_1753_);
                leanh::lean_ctor_set(v___x_1754_, 1, v___x_1753_);
                leanh::lean_ctor_set(v___x_1754_, 2, v___x_1753_);
                return v___x_1754_;
            }
            2 => {
                v___x_1760_ = lean_nat_dec_le(v___y_1759_, v___x_1757_);
                if v___x_1760_ == 0 {
                    leanh::lean_dec(v___x_1757_);
                    leanh::lean_inc(v___y_1759_);
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
    mut v___x_1763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1765_, 0, v___x_1763_);
    return v___x_1765_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v___x_1766_: *mut leanh::LeanObject,
    mut v___y_1767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___lam__6_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_(v___x_1766_);
    return v_res_1768_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn___closed__19_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_;
    v___x_1817_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_1816_);
    return v___x_1817_;
}
pub unsafe fn l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2____boxed(
    mut v_a_1818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1819_ = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_();
    return v_res_1819_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0(
    mut v_00_u03c3_1820_: *mut leanh::LeanObject,
    mut v_00_u03b2_1821_: *mut leanh::LeanObject,
    mut v_map_1822_: *mut leanh::LeanObject,
    mut v_f_1823_: *mut leanh::LeanObject,
    mut v_init_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___redArg(v_map_1822_, v_f_1823_, v_init_1824_);
    return v___x_1825_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03c3_1826_: *mut leanh::LeanObject,
    mut v_00_u03b2_1827_: *mut leanh::LeanObject,
    mut v_map_1828_: *mut leanh::LeanObject,
    mut v_f_1829_: *mut leanh::LeanObject,
    mut v_init_1830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1831_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0(v_00_u03c3_1826_, v_00_u03b2_1827_, v_map_1828_, v_f_1829_, v_init_1830_);
    leanh::lean_dec_ref(v_map_1828_);
    return v_res_1831_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2(
    mut v_n_1832_: *mut leanh::LeanObject,
    mut v_as_1833_: *mut leanh::LeanObject,
    mut v_lo_1834_: *mut leanh::LeanObject,
    mut v_hi_1835_: *mut leanh::LeanObject,
    mut v_w_1836_: *mut leanh::LeanObject,
    mut v_hlo_1837_: *mut leanh::LeanObject,
    mut v_hhi_1838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1839_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___redArg(v_n_1832_, v_as_1833_, v_lo_1834_, v_hi_1835_);
    return v___x_1839_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2___boxed(
    mut v_n_1840_: *mut leanh::LeanObject,
    mut v_as_1841_: *mut leanh::LeanObject,
    mut v_lo_1842_: *mut leanh::LeanObject,
    mut v_hi_1843_: *mut leanh::LeanObject,
    mut v_w_1844_: *mut leanh::LeanObject,
    mut v_hlo_1845_: *mut leanh::LeanObject,
    mut v_hhi_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2(v_n_1840_, v_as_1841_, v_lo_1842_, v_hi_1843_, v_w_1844_, v_hlo_1845_, v_hhi_1846_);
    leanh::lean_dec(v_hi_1843_);
    leanh::lean_dec(v_n_1840_);
    return v_res_1847_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_map_1848_: *mut leanh::LeanObject,
    mut v_f_1849_: *mut leanh::LeanObject,
    mut v_init_1850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1849_, v_map_1848_, v_init_1850_);
    return v___x_1851_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_map_1852_: *mut leanh::LeanObject,
    mut v_f_1853_: *mut leanh::LeanObject,
    mut v_init_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_1852_, v_f_1853_, v_init_1854_);
    leanh::lean_dec_ref(v_map_1852_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03c3_1856_: *mut leanh::LeanObject,
    mut v_00_u03b2_1857_: *mut leanh::LeanObject,
    mut v_map_1858_: *mut leanh::LeanObject,
    mut v_f_1859_: *mut leanh::LeanObject,
    mut v_init_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1859_, v_map_1858_, v_init_1860_);
    return v___x_1861_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03c3_1862_: *mut leanh::LeanObject,
    mut v_00_u03b2_1863_: *mut leanh::LeanObject,
    mut v_map_1864_: *mut leanh::LeanObject,
    mut v_f_1865_: *mut leanh::LeanObject,
    mut v_init_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1867_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_1862_, v_00_u03b2_1863_, v_map_1864_, v_f_1865_, v_init_1866_);
    leanh::lean_dec_ref(v_map_1864_);
    return v_res_1867_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3(
    mut v_n_1868_: *mut leanh::LeanObject,
    mut v_lo_1869_: *mut leanh::LeanObject,
    mut v_hi_1870_: *mut leanh::LeanObject,
    mut v_hhi_1871_: *mut leanh::LeanObject,
    mut v_pivot_1872_: *mut leanh::LeanObject,
    mut v_as_1873_: *mut leanh::LeanObject,
    mut v_i_1874_: *mut leanh::LeanObject,
    mut v_k_1875_: *mut leanh::LeanObject,
    mut v_ilo_1876_: *mut leanh::LeanObject,
    mut v_ik_1877_: *mut leanh::LeanObject,
    mut v_w_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___redArg(v_hi_1870_, v_pivot_1872_, v_as_1873_, v_i_1874_, v_k_1875_);
    return v___x_1879_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3___boxed(
    mut v_n_1880_: *mut leanh::LeanObject,
    mut v_lo_1881_: *mut leanh::LeanObject,
    mut v_hi_1882_: *mut leanh::LeanObject,
    mut v_hhi_1883_: *mut leanh::LeanObject,
    mut v_pivot_1884_: *mut leanh::LeanObject,
    mut v_as_1885_: *mut leanh::LeanObject,
    mut v_i_1886_: *mut leanh::LeanObject,
    mut v_k_1887_: *mut leanh::LeanObject,
    mut v_ilo_1888_: *mut leanh::LeanObject,
    mut v_ik_1889_: *mut leanh::LeanObject,
    mut v_w_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1891_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__2_spec__3(v_n_1880_, v_lo_1881_, v_hi_1882_, v_hhi_1883_, v_pivot_1884_, v_as_1885_, v_i_1886_, v_k_1887_, v_ilo_1888_, v_ik_1889_, v_w_1890_);
    leanh::lean_dec_ref(v_pivot_1884_);
    leanh::lean_dec(v_hi_1882_);
    leanh::lean_dec(v_lo_1881_);
    leanh::lean_dec(v_n_1880_);
    return v_res_1891_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03c3_1892_: *mut leanh::LeanObject,
    mut v_00_u03b1_1893_: *mut leanh::LeanObject,
    mut v_00_u03b2_1894_: *mut leanh::LeanObject,
    mut v_f_1895_: *mut leanh::LeanObject,
    mut v_x_1896_: *mut leanh::LeanObject,
    mut v_x_1897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_1895_, v_x_1896_, v_x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_1899_: *mut leanh::LeanObject,
    mut v_00_u03b1_1900_: *mut leanh::LeanObject,
    mut v_00_u03b2_1901_: *mut leanh::LeanObject,
    mut v_f_1902_: *mut leanh::LeanObject,
    mut v_x_1903_: *mut leanh::LeanObject,
    mut v_x_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_1899_, v_00_u03b1_1900_, v_00_u03b2_1901_, v_f_1902_, v_x_1903_, v_x_1904_);
    leanh::lean_dec_ref(v_x_1903_);
    return v_res_1905_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1906_: *mut leanh::LeanObject,
    mut v_00_u03b2_1907_: *mut leanh::LeanObject,
    mut v_00_u03c3_1908_: *mut leanh::LeanObject,
    mut v_f_1909_: *mut leanh::LeanObject,
    mut v_as_1910_: *mut leanh::LeanObject,
    mut v_i_1911_: usize,
    mut v_stop_1912_: usize,
    mut v_b_1913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_1909_, v_as_1910_, v_i_1911_, v_stop_1912_, v_b_1913_);
    return v___x_1914_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1915_: *mut leanh::LeanObject,
    mut v_00_u03b2_1916_: *mut leanh::LeanObject,
    mut v_00_u03c3_1917_: *mut leanh::LeanObject,
    mut v_f_1918_: *mut leanh::LeanObject,
    mut v_as_1919_: *mut leanh::LeanObject,
    mut v_i_1920_: *mut leanh::LeanObject,
    mut v_stop_1921_: *mut leanh::LeanObject,
    mut v_b_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1923_: usize = 0;
    let mut v_stop_boxed_1924_: usize = 0;
    let mut v_res_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1923_ = leanh::lean_unbox_usize(v_i_1920_);
    leanh::lean_dec(v_i_1920_);
    v_stop_boxed_1924_ = leanh::lean_unbox_usize(v_stop_1921_);
    leanh::lean_dec(v_stop_1921_);
    v_res_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1915_, v_00_u03b2_1916_, v_00_u03c3_1917_, v_f_1918_, v_as_1919_, v_i_boxed_1923_, v_stop_boxed_1924_, v_b_1922_);
    leanh::lean_dec_ref(v_as_1919_);
    return v_res_1925_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03c3_1926_: *mut leanh::LeanObject,
    mut v_00_u03b1_1927_: *mut leanh::LeanObject,
    mut v_00_u03b2_1928_: *mut leanh::LeanObject,
    mut v_f_1929_: *mut leanh::LeanObject,
    mut v_keys_1930_: *mut leanh::LeanObject,
    mut v_vals_1931_: *mut leanh::LeanObject,
    mut v_heq_1932_: *mut leanh::LeanObject,
    mut v_i_1933_: *mut leanh::LeanObject,
    mut v_acc_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1935_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_f_1929_, v_keys_1930_, v_vals_1931_, v_i_1933_, v_acc_1934_);
    return v___x_1935_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03c3_1936_: *mut leanh::LeanObject,
    mut v_00_u03b1_1937_: *mut leanh::LeanObject,
    mut v_00_u03b2_1938_: *mut leanh::LeanObject,
    mut v_f_1939_: *mut leanh::LeanObject,
    mut v_keys_1940_: *mut leanh::LeanObject,
    mut v_vals_1941_: *mut leanh::LeanObject,
    mut v_heq_1942_: *mut leanh::LeanObject,
    mut v_i_1943_: *mut leanh::LeanObject,
    mut v_acc_1944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03c3_1936_, v_00_u03b1_1937_, v_00_u03b2_1938_, v_f_1939_, v_keys_1940_, v_vals_1941_, v_heq_1942_, v_i_1943_, v_acc_1944_);
    leanh::lean_dec_ref(v_vals_1941_);
    leanh::lean_dec_ref(v_keys_1940_);
    return v_res_1945_;
}
pub unsafe fn l_Lean_collectAxioms___redArg___lam__0(
    mut v___x_1946_: *mut leanh::LeanObject,
    mut v_constName_1947_: *mut leanh::LeanObject,
    mut v_toPure_1948_: *mut leanh::LeanObject,
    mut v_env_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1950_: u8 = 0;
    let mut v_privateEnv_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1950_ = 0;
    leanh::lean_inc_ref(v_env_1949_);
    v_privateEnv_1951_ = l_Lean_Environment_setExporting(v_env_1949_, v___x_1950_);
    v___x_1952_ = l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt;
    v___x_1953_ = leanh::lean_box(2);
    v___x_1954_ = leanh::lean_box(0);
    v_s_1955_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_1946_,
        v___x_1952_,
        v_env_1949_,
        v___x_1953_,
        v___x_1954_,
    );
    v___x_1956_ = leanh::lean_alloc_closure(
        l___private_Lean_Util_CollectAxioms_0__Lean_ExportedAxiomsState_find_x3f___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___x_1956_, 0, v_s_1955_);
    v___x_1957_ = leanh::lean_alloc_closure(
        l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_collectAndGet___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_1957_, 0, v___x_1956_);
    leanh::lean_closure_set(v___x_1957_, 1, v_constName_1947_);
    v___x_1958_ = l___private_Lean_Util_CollectAxioms_0__Lean_CollectAxioms_runM___redArg(
        v_privateEnv_1951_,
        v___x_1957_,
    );
    v___x_1959_ =
        leanh::lean_apply_2(v_toPure_1948_, leanh::lean_box(0), v___x_1958_);
    return v___x_1959_;
}
pub unsafe fn l_Lean_collectAxioms___redArg(
    mut v_inst_1960_: *mut leanh::LeanObject,
    mut v_inst_1961_: *mut leanh::LeanObject,
    mut v_constName_1962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1963_ = leanh::lean_ctor_get(v_inst_1960_, 0);
    leanh::lean_inc_ref(v_toApplicative_1963_);
    v_toBind_1964_ = leanh::lean_ctor_get(v_inst_1960_, 1);
    leanh::lean_inc(v_toBind_1964_);
    leanh::lean_dec_ref(v_inst_1960_);
    v_getEnv_1965_ = leanh::lean_ctor_get(v_inst_1961_, 0);
    leanh::lean_inc(v_getEnv_1965_);
    leanh::lean_dec_ref(v_inst_1961_);
    v_toPure_1966_ = leanh::lean_ctor_get(v_toApplicative_1963_, 1);
    leanh::lean_inc(v_toPure_1966_);
    leanh::lean_dec_ref(v_toApplicative_1963_);
    v___x_1967_ = l___private_Lean_Util_CollectAxioms_0__Lean_instInhabitedExportedAxiomsState;
    v___f_1968_ = leanh::lean_alloc_closure(
        l_Lean_collectAxioms___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1968_, 0, v___x_1967_);
    leanh::lean_closure_set(v___f_1968_, 1, v_constName_1962_);
    leanh::lean_closure_set(v___f_1968_, 2, v_toPure_1966_);
    v___x_1969_ = leanh::lean_apply_4(
        v_toBind_1964_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_1965_,
        v___f_1968_,
    );
    return v___x_1969_;
}
pub unsafe fn l_Lean_collectAxioms(
    mut v_m_1970_: *mut leanh::LeanObject,
    mut v_inst_1971_: *mut leanh::LeanObject,
    mut v_inst_1972_: *mut leanh::LeanObject,
    mut v_constName_1973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1974_ = l_Lean_collectAxioms___redArg(v_inst_1971_, v_inst_1972_, v_constName_1973_);
    return v___x_1974_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_CollectAxioms(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_MonadEnv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_CollectAxioms_0__Lean_initFn_00___x40_Lean_Util_CollectAxioms_751524320____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(
        l___private_Lean_Util_CollectAxioms_0__Lean_exportedAxiomsExt,
    );
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_CollectAxioms(
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
pub unsafe fn initialize_Lean_Util_CollectAxioms(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_MonadEnv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectAxioms(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_CollectAxioms(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_CollectAxioms(builtin);
}