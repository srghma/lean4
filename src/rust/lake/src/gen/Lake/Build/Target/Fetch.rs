// Lean compiler output
// Module: Lake.Build.Target.Fetch
// Imports: Lake.Build.Infos Lake.Build.Job.Monad Lake.Config.Monad Lake.Build.Key
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget_borrowed, lean_name_eq,
    lean_string_append, lean_task_pure, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map,
};
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_str___override, l_ReaderT_instMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadBaseIO;
use crate::r#gen::Lake::Build::Infos::{
    initialize_Lake_Build_Infos, l_Lake_instDataKindModule, l_Lake_instDataKindPackage,
    runtime_initialize_Lake_Build_Infos,
};
use crate::r#gen::Lake::Build::Job::Basic::l_Lake_Job_toOpaque___redArg;
use crate::r#gen::Lake::Build::Job::Monad::{
    initialize_Lake_Build_Job_Monad, l_Lake_Job_bindM___redArg, l_Lake_Job_collectArray___redArg,
    runtime_initialize_Lake_Build_Job_Monad,
};
use crate::r#gen::Lake::Build::Key::{
    initialize_Lake_Build_Key, l_Lake_BuildKey_toString, l_Lake_PartialBuildKey_toString,
    runtime_initialize_Lake_Build_Key,
};
use crate::r#gen::Lake::Build::Trace::l_Lake_BuildTrace_nil;
use crate::r#gen::Lake::Config::FacetConfig::l_Lake_FacetConfigMap_get_x3f;
use crate::r#gen::Lake::Config::LeanExe::l_Lake_Package_findTargetModule_x3f;
use crate::r#gen::Lake::Config::Monad::{
    initialize_Lake_Config_Monad, runtime_initialize_Lake_Config_Monad,
};
use crate::r#gen::Lake::Config::Package::l_Lake_Package_findTargetDecl_x3f;
use crate::r#gen::Lake::Config::Workspace::l_Lake_Workspace_findModule_x3f;
use crate::r#gen::Lake::Util::EStateT::{
    l_Lake_EStateT_instFunctor___redArg, l_Lake_EStateT_instMonad___redArg___lam__1,
    l_Lake_EStateT_instMonad___redArg___lam__3, l_Lake_EStateT_instMonad___redArg___lam__5,
    l_Lake_EStateT_instMonad___redArg___lam__9, l_Lake_EStateT_instPure___redArg___lam__0,
};
use crate::r#gen::Lake::Util::EquipT::l_Lake_EquipT_instMonad___redArg;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl,
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_get_x3f___redArg;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [39, 58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [39, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 119, 111, 114, 107, 115, 112, 97, 99, 101, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12_value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [60, 110, 105, 108, 62, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [39, 58, 32, 109, 111, 100, 117, 108, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [39, 58, 32, 109, 111, 100, 117, 108, 101, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [39, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [39, 58, 32, 116, 97, 114, 103, 101, 116, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [39, 58, 32, 117, 110, 107, 110, 111, 119, 110, 32, 102, 97, 99, 101, 116, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9_value) as *mut crate::leanh::LeanObject,9666231177748665885 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [39, 58, 32, 116, 97, 114, 103, 101, 116, 115, 32, 111, 102, 32, 111, 112, 97, 113, 117, 101, 32, 100, 97, 116, 97, 32, 107, 105, 110, 100, 115, 32, 100, 111, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 32, 102, 97, 99, 101, 116, 115, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Target_fetchIn___redArg___closed__0_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 116,
            97, 114, 103, 101, 116, 32, 39, 0,
        ],
    };
static mut l_Lake_Target_fetchIn___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Target_fetchIn___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Target_fetchIn___redArg___closed__1_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [39, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0],
    };
static mut l_Lake_Target_fetchIn___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Target_fetchIn___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Target_fetchIn___redArg___closed__2_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [39, 44, 32, 103, 111, 116, 32, 0],
    };
static mut l_Lake_Target_fetchIn___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Target_fetchIn___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_Target_fetchIn___redArg___closed__3_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [117, 110, 107, 110, 111, 119, 110, 0],
    };
static mut l_Lake_Target_fetchIn___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Target_fetchIn___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(
    mut v_name_1365_: *mut crate::leanh::LeanObject,
    mut v___x_1366_: *mut crate::leanh::LeanObject,
    mut v___x_1367_: *mut crate::leanh::LeanObject,
    mut v_a_1368_: *mut crate::leanh::LeanObject,
    mut v_x_1369_: *mut crate::leanh::LeanObject,
    mut v___y_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_baseName_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    v_baseName_1371_ = crate::leanh::lean_ctor_get(v_a_1368_, 1);
    v___x_1372_ = lean_name_eq(v_baseName_1371_, v_name_1365_);
    if v___x_1372_ == 0 {
        let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_a_1368_);
        v___x_1373_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1373_, 0, v___x_1366_);
        return v___x_1373_;
    } else {
        let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1366_);
        v___x_1374_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1374_, 0, v_a_1368_);
        v___x_1375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1375_, 0, v___x_1374_);
        v___x_1376_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1376_, 0, v___x_1375_);
        crate::leanh::lean_ctor_set(v___x_1376_, 1, v___x_1367_);
        v___x_1377_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1377_, 0, v___x_1376_);
        return v___x_1377_;
    }
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed(
    mut v_name_1378_: *mut crate::leanh::LeanObject,
    mut v___x_1379_: *mut crate::leanh::LeanObject,
    mut v___x_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
    mut v_x_1382_: *mut crate::leanh::LeanObject,
    mut v___y_1383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1384_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(v_name_1378_, v___x_1379_, v___x_1380_, v_a_1381_, v_x_1382_, v___y_1383_);
    crate::leanh::lean_dec_ref(v___y_1383_);
    crate::leanh::lean_dec(v_name_1378_);
    return v_res_1384_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(
    mut v_defaultPkg_1411_: *mut crate::leanh::LeanObject,
    mut v_root_1412_: *mut crate::leanh::LeanObject,
    mut v_name_1413_: *mut crate::leanh::LeanObject,
    mut v_a_1414_: *mut crate::leanh::LeanObject,
    mut v_a_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1462_: usize = 0;
    let mut v___x_1463_: usize = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v_val_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1474_: u8 = 0;
    let mut v_unused_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_name_1413_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_root_1412_);
                    v___x_1434_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1434_, 0, v_defaultPkg_1411_);
                    crate::leanh::lean_ctor_set(v___x_1434_, 1, v_a_1415_);
                    return v___x_1434_;
                }
                2 => {
                    crate::leanh::lean_dec_ref(v_defaultPkg_1411_);
                    v_toContext_1435_ = crate::leanh::lean_ctor_get(v_a_1414_, 1);
                    v_packageMap_1436_ = crate::leanh::lean_ctor_get(v_toContext_1435_, 5);
                    v___x_1437_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3;
                    crate::leanh::lean_inc_ref(v_name_1413_);
                    crate::leanh::lean_inc(v_packageMap_1436_);
                    v___x_1438_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                        v___x_1437_,
                        v_packageMap_1436_,
                        v_name_1413_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1438_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_name_1413_, 2);
                        crate::leanh::lean_dec_ref(v_root_1412_);
                        v_val_1439_ = crate::leanh::lean_ctor_get(v___x_1438_, 0);
                        crate::leanh::lean_inc(v_val_1439_);
                        crate::leanh::lean_dec_ref_known(v___x_1438_, 1);
                        v___x_1440_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1440_, 0, v_val_1439_);
                        crate::leanh::lean_ctor_set(v___x_1440_, 1, v_a_1415_);
                        return v___x_1440_;
                    } else {
                        crate::leanh::lean_dec(v___x_1438_);
                        v___x_1441_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_1442_ = l_Lake_PartialBuildKey_toString(v_root_1412_);
                        v___x_1443_ = lean_string_append(v___x_1441_, v___x_1442_);
                        crate::leanh::lean_dec_ref(v___x_1442_);
                        v___x_1444_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                        v___x_1445_ = lean_string_append(v___x_1443_, v___x_1444_);
                        v___x_1446_ = 1;
                        v___x_1447_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_1413_,
                                v___x_1446_,
                            );
                        v___x_1448_ = lean_string_append(v___x_1445_, v___x_1447_);
                        crate::leanh::lean_dec_ref(v___x_1447_);
                        v___x_1449_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                        v___x_1450_ = lean_string_append(v___x_1448_, v___x_1449_);
                        v___x_1451_ = 3;
                        v___x_1452_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1452_, 0, v___x_1450_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1452_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1451_,
                        );
                        v___x_1453_ = lean_array_get_size(v_a_1415_);
                        v___x_1454_ = lean_array_push(v_a_1415_, v___x_1452_);
                        v___x_1455_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1455_, 0, v___x_1453_);
                        crate::leanh::lean_ctor_set(v___x_1455_, 1, v___x_1454_);
                        return v___x_1455_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_defaultPkg_1411_);
                    v_toContext_1456_ = crate::leanh::lean_ctor_get(v_a_1414_, 1);
                    v_packages_1457_ = crate::leanh::lean_ctor_get(v_toContext_1456_, 4);
                    v___x_1458_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13;
                    v___x_1459_ = crate::leanh::lean_box(0);
                    v___x_1460_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                    crate::leanh::lean_inc(v_name_1413_);
                    v___f_1461_ = crate::leanh::lean_alloc_closure(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 3);
                    crate::leanh::lean_closure_set(v___f_1461_, 0, v_name_1413_);
                    crate::leanh::lean_closure_set(v___f_1461_, 1, v___x_1460_);
                    crate::leanh::lean_closure_set(v___f_1461_, 2, v___x_1459_);
                    v_sz_1462_ = lean_array_size(v_packages_1457_);
                    v___x_1463_ = 0usize;
                    crate::leanh::lean_inc_ref(v_packages_1457_);
                    v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1458_,
                        v_packages_1457_,
                        v___f_1461_,
                        v_sz_1462_,
                        v___x_1463_,
                        v___x_1460_,
                    );
                    v_fst_1465_ = crate::leanh::lean_ctor_get(v___x_1464_, 0);
                    v_isSharedCheck_1474_ = (!crate::leanh::lean_is_exclusive(v___x_1464_)) as u8;
                    if v_isSharedCheck_1474_ == 0 {
                        v_unused_1475_ = crate::leanh::lean_ctor_get(v___x_1464_, 1);
                        crate::leanh::lean_dec(v_unused_1475_);
                        v___x_1467_ = v___x_1464_;
                        v_isShared_1468_ = v_isSharedCheck_1474_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_1465_);
                        crate::leanh::lean_dec(v___x_1464_);
                        v___x_1467_ = crate::leanh::lean_box(0);
                        v_isShared_1468_ = v_isSharedCheck_1474_;
                        state = 2;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1419_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                v___x_1420_ = l_Lake_PartialBuildKey_toString(v_root_1412_);
                v___x_1421_ = lean_string_append(v___x_1419_, v___x_1420_);
                crate::leanh::lean_dec_ref(v___x_1420_);
                v___x_1422_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                v___x_1423_ = lean_string_append(v___x_1421_, v___x_1422_);
                v___x_1424_ = 1;
                v___x_1425_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_1413_,
                    v___x_1424_,
                );
                v___x_1426_ = lean_string_append(v___x_1423_, v___x_1425_);
                crate::leanh::lean_dec_ref(v___x_1425_);
                v___x_1427_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                v___x_1428_ = lean_string_append(v___x_1426_, v___x_1427_);
                v___x_1429_ = 3;
                v___x_1430_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1430_, 0, v___x_1428_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1430_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1429_,
                );
                v___x_1431_ = lean_array_get_size(v_a_1418_);
                v___x_1432_ = lean_array_push(v_a_1418_, v___x_1430_);
                v___x_1433_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1433_, 0, v___x_1431_);
                crate::leanh::lean_ctor_set(v___x_1433_, 1, v___x_1432_);
                return v___x_1433_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_fst_1465_) == 0 {
                    crate::leanh::lean_del_object(v___x_1467_);
                    v_a_1418_ = v_a_1415_;
                    state = 1;
                    continue;
                } else {
                    v_val_1469_ = crate::leanh::lean_ctor_get(v_fst_1465_, 0);
                    crate::leanh::lean_inc(v_val_1469_);
                    crate::leanh::lean_dec_ref_known(v_fst_1465_, 1);
                    if crate::leanh::lean_obj_tag(v_val_1469_) == 1 {
                        crate::leanh::lean_dec(v_name_1413_);
                        crate::leanh::lean_dec_ref(v_root_1412_);
                        v_val_1470_ = crate::leanh::lean_ctor_get(v_val_1469_, 0);
                        crate::leanh::lean_inc(v_val_1470_);
                        crate::leanh::lean_dec_ref_known(v_val_1469_, 1);
                        if v_isShared_1468_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1467_, 1, v_a_1415_);
                            crate::leanh::lean_ctor_set(v___x_1467_, 0, v_val_1470_);
                            v___x_1472_ = v___x_1467_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1473_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_val_1470_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_a_1415_);
                            v___x_1472_ = v_reuseFailAlloc_1473_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1469_);
                        crate::leanh::lean_del_object(v___x_1467_);
                        v_a_1418_ = v_a_1415_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___boxed(
    mut v_defaultPkg_1476_: *mut crate::leanh::LeanObject,
    mut v_root_1477_: *mut crate::leanh::LeanObject,
    mut v_name_1478_: *mut crate::leanh::LeanObject,
    mut v_a_1479_: *mut crate::leanh::LeanObject,
    mut v_a_1480_: *mut crate::leanh::LeanObject,
    mut v_a_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1482_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(v_defaultPkg_1476_, v_root_1477_, v_name_1478_, v_a_1479_, v_a_1480_);
    crate::leanh::lean_dec_ref(v_a_1479_);
    return v_res_1482_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(
    mut v_defaultPkg_1483_: *mut crate::leanh::LeanObject,
    mut v_root_1484_: *mut crate::leanh::LeanObject,
    mut v_name_1485_: *mut crate::leanh::LeanObject,
    mut v_a_1486_: *mut crate::leanh::LeanObject,
    mut v_a_1487_: *mut crate::leanh::LeanObject,
    mut v_a_1488_: *mut crate::leanh::LeanObject,
    mut v_a_1489_: *mut crate::leanh::LeanObject,
    mut v_a_1490_: *mut crate::leanh::LeanObject,
    mut v_a_1491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: u8 = 0;
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1538_: usize = 0;
    let mut v___x_1539_: usize = 0;
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1544_: u8 = 0;
    let mut v_val_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1550_: u8 = 0;
    let mut v_unused_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_name_1485_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_root_1484_);
                    v___x_1510_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1510_, 0, v_defaultPkg_1483_);
                    crate::leanh::lean_ctor_set(v___x_1510_, 1, v_a_1491_);
                    return v___x_1510_;
                }
                2 => {
                    crate::leanh::lean_dec_ref(v_defaultPkg_1483_);
                    v_toContext_1511_ = crate::leanh::lean_ctor_get(v_a_1490_, 1);
                    v_packageMap_1512_ = crate::leanh::lean_ctor_get(v_toContext_1511_, 5);
                    v___x_1513_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3;
                    crate::leanh::lean_inc_ref(v_name_1485_);
                    crate::leanh::lean_inc(v_packageMap_1512_);
                    v___x_1514_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                        v___x_1513_,
                        v_packageMap_1512_,
                        v_name_1485_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1514_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_name_1485_, 2);
                        crate::leanh::lean_dec_ref(v_root_1484_);
                        v_val_1515_ = crate::leanh::lean_ctor_get(v___x_1514_, 0);
                        crate::leanh::lean_inc(v_val_1515_);
                        crate::leanh::lean_dec_ref_known(v___x_1514_, 1);
                        v___x_1516_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1516_, 0, v_val_1515_);
                        crate::leanh::lean_ctor_set(v___x_1516_, 1, v_a_1491_);
                        return v___x_1516_;
                    } else {
                        crate::leanh::lean_dec(v___x_1514_);
                        v___x_1517_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_1518_ = l_Lake_PartialBuildKey_toString(v_root_1484_);
                        v___x_1519_ = lean_string_append(v___x_1517_, v___x_1518_);
                        crate::leanh::lean_dec_ref(v___x_1518_);
                        v___x_1520_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                        v___x_1521_ = lean_string_append(v___x_1519_, v___x_1520_);
                        v___x_1522_ = 1;
                        v___x_1523_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_1485_,
                                v___x_1522_,
                            );
                        v___x_1524_ = lean_string_append(v___x_1521_, v___x_1523_);
                        crate::leanh::lean_dec_ref(v___x_1523_);
                        v___x_1525_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                        v___x_1526_ = lean_string_append(v___x_1524_, v___x_1525_);
                        v___x_1527_ = 3;
                        v___x_1528_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1526_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1528_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1527_,
                        );
                        v___x_1529_ = lean_array_get_size(v_a_1491_);
                        v___x_1530_ = lean_array_push(v_a_1491_, v___x_1528_);
                        v___x_1531_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1531_, 0, v___x_1529_);
                        crate::leanh::lean_ctor_set(v___x_1531_, 1, v___x_1530_);
                        return v___x_1531_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_defaultPkg_1483_);
                    v_toContext_1532_ = crate::leanh::lean_ctor_get(v_a_1490_, 1);
                    v_packages_1533_ = crate::leanh::lean_ctor_get(v_toContext_1532_, 4);
                    v___x_1534_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13;
                    v___x_1535_ = crate::leanh::lean_box(0);
                    v___x_1536_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                    crate::leanh::lean_inc(v_name_1485_);
                    v___f_1537_ = crate::leanh::lean_alloc_closure(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 3);
                    crate::leanh::lean_closure_set(v___f_1537_, 0, v_name_1485_);
                    crate::leanh::lean_closure_set(v___f_1537_, 1, v___x_1536_);
                    crate::leanh::lean_closure_set(v___f_1537_, 2, v___x_1535_);
                    v_sz_1538_ = lean_array_size(v_packages_1533_);
                    v___x_1539_ = 0usize;
                    crate::leanh::lean_inc_ref(v_packages_1533_);
                    v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_1534_,
                        v_packages_1533_,
                        v___f_1537_,
                        v_sz_1538_,
                        v___x_1539_,
                        v___x_1536_,
                    );
                    v_fst_1541_ = crate::leanh::lean_ctor_get(v___x_1540_, 0);
                    v_isSharedCheck_1550_ = (!crate::leanh::lean_is_exclusive(v___x_1540_)) as u8;
                    if v_isSharedCheck_1550_ == 0 {
                        v_unused_1551_ = crate::leanh::lean_ctor_get(v___x_1540_, 1);
                        crate::leanh::lean_dec(v_unused_1551_);
                        v___x_1543_ = v___x_1540_;
                        v_isShared_1544_ = v_isSharedCheck_1550_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_1541_);
                        crate::leanh::lean_dec(v___x_1540_);
                        v___x_1543_ = crate::leanh::lean_box(0);
                        v_isShared_1544_ = v_isSharedCheck_1550_;
                        state = 2;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1495_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                v___x_1496_ = l_Lake_PartialBuildKey_toString(v_root_1484_);
                v___x_1497_ = lean_string_append(v___x_1495_, v___x_1496_);
                crate::leanh::lean_dec_ref(v___x_1496_);
                v___x_1498_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                v___x_1499_ = lean_string_append(v___x_1497_, v___x_1498_);
                v___x_1500_ = 1;
                v___x_1501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_1485_,
                    v___x_1500_,
                );
                v___x_1502_ = lean_string_append(v___x_1499_, v___x_1501_);
                crate::leanh::lean_dec_ref(v___x_1501_);
                v___x_1503_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                v___x_1504_ = lean_string_append(v___x_1502_, v___x_1503_);
                v___x_1505_ = 3;
                v___x_1506_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1506_, 0, v___x_1504_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1506_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1505_,
                );
                v___x_1507_ = lean_array_get_size(v_a_1494_);
                v___x_1508_ = lean_array_push(v_a_1494_, v___x_1506_);
                v___x_1509_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1509_, 0, v___x_1507_);
                crate::leanh::lean_ctor_set(v___x_1509_, 1, v___x_1508_);
                return v___x_1509_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_fst_1541_) == 0 {
                    crate::leanh::lean_del_object(v___x_1543_);
                    v_a_1494_ = v_a_1491_;
                    state = 1;
                    continue;
                } else {
                    v_val_1545_ = crate::leanh::lean_ctor_get(v_fst_1541_, 0);
                    crate::leanh::lean_inc(v_val_1545_);
                    crate::leanh::lean_dec_ref_known(v_fst_1541_, 1);
                    if crate::leanh::lean_obj_tag(v_val_1545_) == 1 {
                        crate::leanh::lean_dec(v_name_1485_);
                        crate::leanh::lean_dec_ref(v_root_1484_);
                        v_val_1546_ = crate::leanh::lean_ctor_get(v_val_1545_, 0);
                        crate::leanh::lean_inc(v_val_1546_);
                        crate::leanh::lean_dec_ref_known(v_val_1545_, 1);
                        if v_isShared_1544_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1543_, 1, v_a_1491_);
                            crate::leanh::lean_ctor_set(v___x_1543_, 0, v_val_1546_);
                            v___x_1548_ = v___x_1543_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1549_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_val_1546_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_a_1491_);
                            v___x_1548_ = v_reuseFailAlloc_1549_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1545_);
                        crate::leanh::lean_del_object(v___x_1543_);
                        v_a_1494_ = v_a_1491_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___boxed(
    mut v_defaultPkg_1552_: *mut crate::leanh::LeanObject,
    mut v_root_1553_: *mut crate::leanh::LeanObject,
    mut v_name_1554_: *mut crate::leanh::LeanObject,
    mut v_a_1555_: *mut crate::leanh::LeanObject,
    mut v_a_1556_: *mut crate::leanh::LeanObject,
    mut v_a_1557_: *mut crate::leanh::LeanObject,
    mut v_a_1558_: *mut crate::leanh::LeanObject,
    mut v_a_1559_: *mut crate::leanh::LeanObject,
    mut v_a_1560_: *mut crate::leanh::LeanObject,
    mut v_a_1561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1562_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(v_defaultPkg_1552_, v_root_1553_, v_name_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
    crate::leanh::lean_dec_ref(v_a_1559_);
    crate::leanh::lean_dec(v_a_1558_);
    crate::leanh::lean_dec(v_a_1557_);
    crate::leanh::lean_dec(v_a_1556_);
    crate::leanh::lean_dec_ref(v_a_1555_);
    return v_res_1562_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(
    mut v_target_1563_: *mut crate::leanh::LeanObject,
    mut v_kind_1564_: *mut crate::leanh::LeanObject,
    mut v___x_1565_: *mut crate::leanh::LeanObject,
    mut v_data_1566_: *mut crate::leanh::LeanObject,
    mut v___y_1567_: *mut crate::leanh::LeanObject,
    mut v___y_1568_: *mut crate::leanh::LeanObject,
    mut v___y_1569_: *mut crate::leanh::LeanObject,
    mut v___y_1570_: *mut crate::leanh::LeanObject,
    mut v___y_1571_: *mut crate::leanh::LeanObject,
    mut v___y_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_1575_: u8 = 0;
    let mut v_wantsRebuild_1576_: u8 = 0;
    let mut v_trace_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1581_: u8 = 0;
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_a_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_1574_ = crate::leanh::lean_ctor_get(v___y_1572_, 0);
                v_action_1575_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1572_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_1576_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_1572_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_1577_ = crate::leanh::lean_ctor_get(v___y_1572_, 1);
                v_buildTime_1578_ = crate::leanh::lean_ctor_get(v___y_1572_, 2);
                v_isSharedCheck_1608_ = (!crate::leanh::lean_is_exclusive(v___y_1572_)) as u8;
                if v_isSharedCheck_1608_ == 0 {
                    v___x_1580_ = v___y_1572_;
                    v_isShared_1581_ = v_isSharedCheck_1608_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_1578_);
                    crate::leanh::lean_inc(v_trace_1577_);
                    crate::leanh::lean_inc(v_log_1574_);
                    crate::leanh::lean_dec(v___y_1572_);
                    v___x_1580_ = crate::leanh::lean_box(0);
                    v_isShared_1581_ = v_isSharedCheck_1608_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1582_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1582_, 0, v_target_1563_);
                crate::leanh::lean_ctor_set(v___x_1582_, 1, v_kind_1564_);
                crate::leanh::lean_ctor_set(v___x_1582_, 2, v_data_1566_);
                crate::leanh::lean_ctor_set(v___x_1582_, 3, v___x_1565_);
                crate::leanh::lean_inc_ref(v___y_1571_);
                crate::leanh::lean_inc(v___y_1570_);
                crate::leanh::lean_inc(v___y_1569_);
                crate::leanh::lean_inc(v___y_1568_);
                v___x_1583_ = crate::leanh::lean_apply_7(
                    v___y_1567_,
                    v___x_1582_,
                    v___y_1568_,
                    v___y_1569_,
                    v___y_1570_,
                    v___y_1571_,
                    v_log_1574_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1583_) == 0 {
                    v_a_1584_ = crate::leanh::lean_ctor_get(v___x_1583_, 0);
                    v_a_1585_ = crate::leanh::lean_ctor_get(v___x_1583_, 1);
                    v_isSharedCheck_1595_ = (!crate::leanh::lean_is_exclusive(v___x_1583_)) as u8;
                    if v_isSharedCheck_1595_ == 0 {
                        v___x_1587_ = v___x_1583_;
                        v_isShared_1588_ = v_isSharedCheck_1595_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1585_);
                        crate::leanh::lean_inc(v_a_1584_);
                        crate::leanh::lean_dec(v___x_1583_);
                        v___x_1587_ = crate::leanh::lean_box(0);
                        v_isShared_1588_ = v_isSharedCheck_1595_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1596_ = crate::leanh::lean_ctor_get(v___x_1583_, 0);
                    v_a_1597_ = crate::leanh::lean_ctor_get(v___x_1583_, 1);
                    v_isSharedCheck_1607_ = (!crate::leanh::lean_is_exclusive(v___x_1583_)) as u8;
                    if v_isSharedCheck_1607_ == 0 {
                        v___x_1599_ = v___x_1583_;
                        v_isShared_1600_ = v_isSharedCheck_1607_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1597_);
                        crate::leanh::lean_inc(v_a_1596_);
                        crate::leanh::lean_dec(v___x_1583_);
                        v___x_1599_ = crate::leanh::lean_box(0);
                        v_isShared_1600_ = v_isSharedCheck_1607_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1581_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1580_, 0, v_a_1585_);
                    v___x_1590_ = v___x_1580_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1585_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_trace_1577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_buildTime_1578_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1594_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1575_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1594_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1576_,
                    );
                    v___x_1590_ = v_reuseFailAlloc_1594_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1588_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1587_, 1, v___x_1590_);
                    v___x_1592_ = v___x_1587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1590_);
                    v___x_1592_ = v_reuseFailAlloc_1593_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1592_;
            }
            5 => {
                if v_isShared_1581_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1580_, 0, v_a_1597_);
                    v___x_1602_ = v___x_1580_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_trace_1577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_buildTime_1578_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_1575_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1606_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1576_,
                    );
                    v___x_1602_ = v_reuseFailAlloc_1606_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1599_, 1, v___x_1602_);
                    v___x_1604_ = v___x_1599_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___x_1602_);
                    v___x_1604_ = v_reuseFailAlloc_1605_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed(
    mut v_target_1609_: *mut crate::leanh::LeanObject,
    mut v_kind_1610_: *mut crate::leanh::LeanObject,
    mut v___x_1611_: *mut crate::leanh::LeanObject,
    mut v_data_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1620_ =
        l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(
            v_target_1609_,
            v_kind_1610_,
            v___x_1611_,
            v_data_1612_,
            v___y_1613_,
            v___y_1614_,
            v___y_1615_,
            v___y_1616_,
            v___y_1617_,
            v___y_1618_,
        );
    crate::leanh::lean_dec_ref(v___y_1617_);
    crate::leanh::lean_dec(v___y_1616_);
    crate::leanh::lean_dec(v___y_1615_);
    crate::leanh::lean_dec(v___y_1614_);
    return v_res_1620_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(
    mut v_t_1621_: *mut crate::leanh::LeanObject,
    mut v_k_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u8 = 0;
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1621_) == 0 {
                    v_k_1623_ = crate::leanh::lean_ctor_get(v_t_1621_, 1);
                    v_v_1624_ = crate::leanh::lean_ctor_get(v_t_1621_, 2);
                    v_l_1625_ = crate::leanh::lean_ctor_get(v_t_1621_, 3);
                    v_r_1626_ = crate::leanh::lean_ctor_get(v_t_1621_, 4);
                    v___x_1627_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1622_, v_k_1623_);
                    match v___x_1627_ {
                        0 => {
                            v_t_1621_ = v_l_1625_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_1624_);
                            v___x_1629_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1629_, 0, v_v_1624_);
                            return v___x_1629_;
                        }
                        _ => {
                            v_t_1621_ = v_r_1626_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1631_ = crate::leanh::lean_box(0);
                    return v___x_1631_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg___boxed(
    mut v_t_1632_: *mut crate::leanh::LeanObject,
    mut v_k_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1634_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_t_1632_, v_k_1633_);
    crate::leanh::lean_dec(v_k_1633_);
    crate::leanh::lean_dec(v_t_1632_);
    return v_res_1634_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(
    mut v_package_1635_: *mut crate::leanh::LeanObject,
    mut v_as_1636_: *mut crate::leanh::LeanObject,
    mut v_sz_1637_: usize,
    mut v_i_1638_: usize,
    mut v_b_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1640_: u8 = 0;
    let mut v_a_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: u8 = 0;
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: usize = 0;
    let mut v___x_1647_: usize = 0;
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1640_ = lean_usize_dec_lt(v_i_1638_, v_sz_1637_);
                if v___x_1640_ == 0 {
                    crate::leanh::lean_inc_ref(v_b_1639_);
                    return v_b_1639_;
                } else {
                    v_a_1641_ = lean_array_uget_borrowed(v_as_1636_, v_i_1638_);
                    v_baseName_1642_ = crate::leanh::lean_ctor_get(v_a_1641_, 1);
                    v___x_1643_ = crate::leanh::lean_box(0);
                    v___x_1644_ = lean_name_eq(v_baseName_1642_, v_package_1635_);
                    if v___x_1644_ == 0 {
                        v___x_1645_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                        v___x_1646_ = 1usize;
                        v___x_1647_ = lean_usize_add(v_i_1638_, v___x_1646_);
                        v_i_1638_ = v___x_1647_;
                        v_b_1639_ = v___x_1645_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1641_);
                        v___x_1649_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1649_, 0, v_a_1641_);
                        v___x_1650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1650_, 0, v___x_1649_);
                        v___x_1651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1651_, 0, v___x_1650_);
                        crate::leanh::lean_ctor_set(v___x_1651_, 1, v___x_1643_);
                        return v___x_1651_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1___boxed(
    mut v_package_1652_: *mut crate::leanh::LeanObject,
    mut v_as_1653_: *mut crate::leanh::LeanObject,
    mut v_sz_1654_: *mut crate::leanh::LeanObject,
    mut v_i_1655_: *mut crate::leanh::LeanObject,
    mut v_b_1656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1657_: usize = 0;
    let mut v_i_boxed_1658_: usize = 0;
    let mut v_res_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1657_ = crate::leanh::lean_unbox_usize(v_sz_1654_);
    crate::leanh::lean_dec(v_sz_1654_);
    v_i_boxed_1658_ = crate::leanh::lean_unbox_usize(v_i_1655_);
    crate::leanh::lean_dec(v_i_1655_);
    v_res_1659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_1652_, v_as_1653_, v_sz_boxed_1657_, v_i_boxed_1658_, v_b_1656_);
    crate::leanh::lean_dec_ref(v_b_1656_);
    crate::leanh::lean_dec_ref(v_as_1653_);
    crate::leanh::lean_dec(v_package_1652_);
    return v_res_1659_;
}
pub unsafe fn _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1664_ =
        l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2;
    v___x_1665_ = l_Lake_BuildTrace_nil(v___x_1664_);
    return v___x_1665_;
}
pub unsafe fn _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: u8 = 0;
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1666_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1667_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
    v___x_1668_ = 0;
    v___x_1669_ = 0;
    v___x_1670_ =
        l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0;
    v___x_1671_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1671_, 0, v___x_1670_);
    crate::leanh::lean_ctor_set(v___x_1671_, 1, v___x_1667_);
    crate::leanh::lean_ctor_set(v___x_1671_, 2, v___x_1666_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1671_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_1669_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1671_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
        v___x_1668_,
    );
    return v___x_1671_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
    mut v_defaultPkg_1682_: *mut crate::leanh::LeanObject,
    mut v_root_1683_: *mut crate::leanh::LeanObject,
    mut v_self_1684_: *mut crate::leanh::LeanObject,
    mut v_facetless_1685_: u8,
    mut v_a_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
    mut v_a_1688_: *mut crate::leanh::LeanObject,
    mut v_a_1689_: *mut crate::leanh::LeanObject,
    mut v_a_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lib_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v_a_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: u8 = 0;
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1794_: usize = 0;
    let mut v___x_1795_: usize = 0;
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1800_: u8 = 0;
    let mut v_package_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v_a_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: u8 = 0;
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: u8 = 0;
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1881_: usize = 0;
    let mut v___x_1882_: usize = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1887_: u8 = 0;
    let mut v_package_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v_a_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keyName_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_a_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1928_: u8 = 0;
    let mut v___x_1929_: u8 = 0;
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1940_: u8 = 0;
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut v_a_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut v_reuseFailAlloc_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1968_: u8 = 0;
    let mut v_a_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1973_: u8 = 0;
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1977_: u8 = 0;
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v_unused_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: u8 = 0;
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: u8 = 0;
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packages_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2033_: usize = 0;
    let mut v___x_2034_: usize = 0;
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_target_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2044_: u8 = 0;
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v_a_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2055_: u8 = 0;
    let mut v_kind_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_outKind_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: u8 = 0;
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: u8 = 0;
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: u8 = 0;
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut v_unused_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_unused_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1705_ = l_Lake_instDataKindModule;
                match crate::leanh::lean_obj_tag(v_self_1684_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v_a_1686_);
                        crate::leanh::lean_dec_ref(v_defaultPkg_1682_);
                        v_module_1706_ = crate::leanh::lean_ctor_get(v_self_1684_, 0);
                        crate::leanh::lean_inc_n(v_module_1706_, 2);
                        crate::leanh::lean_dec_ref_known(v_self_1684_, 1);
                        v_toContext_1707_ = crate::leanh::lean_ctor_get(v_a_1690_, 1);
                        v___x_1708_ =
                            l_Lake_Workspace_findModule_x3f(v_module_1706_, v_toContext_1707_);
                        if crate::leanh::lean_obj_tag(v___x_1708_) == 1 {
                            crate::leanh::lean_dec_ref(v_root_1683_);
                            v_val_1709_ = crate::leanh::lean_ctor_get(v___x_1708_, 0);
                            crate::leanh::lean_inc(v_val_1709_);
                            crate::leanh::lean_dec_ref_known(v___x_1708_, 1);
                            v_lib_1710_ = crate::leanh::lean_ctor_get(v_val_1709_, 0);
                            v_pkg_1711_ = crate::leanh::lean_ctor_get(v_lib_1710_, 0);
                            v_keyName_1712_ = crate::leanh::lean_ctor_get(v_pkg_1711_, 2);
                            crate::leanh::lean_inc(v_keyName_1712_);
                            v___x_1713_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1713_, 0, v_keyName_1712_);
                            crate::leanh::lean_ctor_set(v___x_1713_, 1, v_module_1706_);
                            v___x_1714_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                            v___x_1715_ = 0;
                            v___x_1716_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                            v___x_1717_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1717_, 0, v_val_1709_);
                            crate::leanh::lean_ctor_set(v___x_1717_, 1, v___x_1716_);
                            v___x_1718_ = lean_task_pure(v___x_1717_);
                            v___x_1719_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_1719_, 0, v___x_1718_);
                            crate::leanh::lean_ctor_set(v___x_1719_, 1, v___x_1705_);
                            crate::leanh::lean_ctor_set(v___x_1719_, 2, v___x_1714_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1719_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                                v___x_1715_,
                            );
                            v___x_1720_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1720_, 0, v___x_1713_);
                            crate::leanh::lean_ctor_set(v___x_1720_, 1, v___x_1719_);
                            v___x_1721_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1721_, 0, v___x_1720_);
                            crate::leanh::lean_ctor_set(v___x_1721_, 1, v_a_1691_);
                            return v___x_1721_;
                        } else {
                            crate::leanh::lean_dec(v___x_1708_);
                            v___x_1722_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                            v___x_1723_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                            v___x_1724_ = lean_string_append(v___x_1722_, v___x_1723_);
                            crate::leanh::lean_dec_ref(v___x_1723_);
                            v___x_1725_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5;
                            v___x_1726_ = lean_string_append(v___x_1724_, v___x_1725_);
                            v___x_1727_ = 1;
                            v___x_1728_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_module_1706_,
                                    v___x_1727_,
                                );
                            v___x_1729_ = lean_string_append(v___x_1726_, v___x_1728_);
                            crate::leanh::lean_dec_ref(v___x_1728_);
                            v___x_1730_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                            v___x_1731_ = lean_string_append(v___x_1729_, v___x_1730_);
                            v___x_1732_ = 3;
                            v___x_1733_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_1733_, 0, v___x_1731_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1733_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_1732_,
                            );
                            v___x_1734_ = lean_array_get_size(v_a_1691_);
                            v___x_1735_ = lean_array_push(v_a_1691_, v___x_1733_);
                            v___x_1736_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1736_, 0, v___x_1734_);
                            crate::leanh::lean_ctor_set(v___x_1736_, 1, v___x_1735_);
                            return v___x_1736_;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_a_1686_);
                        v_package_1737_ = crate::leanh::lean_ctor_get(v_self_1684_, 0);
                        v_isSharedCheck_1800_ =
                            (!crate::leanh::lean_is_exclusive(v_self_1684_)) as u8;
                        if v_isSharedCheck_1800_ == 0 {
                            v___x_1739_ = v_self_1684_;
                            v_isShared_1740_ = v_isSharedCheck_1800_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_package_1737_);
                            crate::leanh::lean_dec(v_self_1684_);
                            v___x_1739_ = crate::leanh::lean_box(0);
                            v_isShared_1740_ = v_isSharedCheck_1800_;
                            state = 4;
                            continue;
                        }
                    }
                    2 => {
                        crate::leanh::lean_dec_ref(v_a_1686_);
                        v_package_1801_ = crate::leanh::lean_ctor_get(v_self_1684_, 0);
                        v_module_1802_ = crate::leanh::lean_ctor_get(v_self_1684_, 1);
                        v_isSharedCheck_1887_ =
                            (!crate::leanh::lean_is_exclusive(v_self_1684_)) as u8;
                        if v_isSharedCheck_1887_ == 0 {
                            v___x_1804_ = v_self_1684_;
                            v_isShared_1805_ = v_isSharedCheck_1887_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_module_1802_);
                            crate::leanh::lean_inc(v_package_1801_);
                            crate::leanh::lean_dec(v_self_1684_);
                            v___x_1804_ = crate::leanh::lean_box(0);
                            v_isShared_1805_ = v_isSharedCheck_1887_;
                            state = 8;
                            continue;
                        }
                    }
                    3 => {
                        v_package_1888_ = crate::leanh::lean_ctor_get(v_self_1684_, 0);
                        v_target_1889_ = crate::leanh::lean_ctor_get(v_self_1684_, 1);
                        v_isSharedCheck_2039_ =
                            (!crate::leanh::lean_is_exclusive(v_self_1684_)) as u8;
                        if v_isSharedCheck_2039_ == 0 {
                            v___x_1891_ = v_self_1684_;
                            v_isShared_1892_ = v_isSharedCheck_2039_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_target_1889_);
                            crate::leanh::lean_inc(v_package_1888_);
                            crate::leanh::lean_dec(v_self_1684_);
                            v___x_1891_ = crate::leanh::lean_box(0);
                            v_isShared_1892_ = v_isSharedCheck_2039_;
                            state = 12;
                            continue;
                        }
                    }
                    _ => {
                        v_target_2040_ = crate::leanh::lean_ctor_get(v_self_1684_, 0);
                        v_facet_2041_ = crate::leanh::lean_ctor_get(v_self_1684_, 1);
                        v_isSharedCheck_2112_ =
                            (!crate::leanh::lean_is_exclusive(v_self_1684_)) as u8;
                        if v_isSharedCheck_2112_ == 0 {
                            v___x_2043_ = v_self_1684_;
                            v_isShared_2044_ = v_isSharedCheck_2112_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_facet_2041_);
                            crate::leanh::lean_inc(v_target_2040_);
                            crate::leanh::lean_dec(v_self_1684_);
                            v___x_2043_ = crate::leanh::lean_box(0);
                            v_isShared_2044_ = v_isSharedCheck_2112_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1696_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1696_, 0, v_a_1694_);
                crate::leanh::lean_ctor_set(v___x_1696_, 1, v_a_1695_);
                return v___x_1696_;
            }
            2 => {
                v___x_1700_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1700_, 0, v_a_1698_);
                crate::leanh::lean_ctor_set(v___x_1700_, 1, v_a_1699_);
                return v___x_1700_;
            }
            3 => {
                v___x_1704_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1704_, 0, v_a_1702_);
                crate::leanh::lean_ctor_set(v___x_1704_, 1, v_a_1703_);
                return v___x_1704_;
            }
            4 => {
                v___x_1757_ = l_Lake_instDataKindPackage;
                match crate::leanh::lean_obj_tag(v_package_1737_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v_root_1683_);
                        v_a_1759_ = v_defaultPkg_1682_;
                        v_a_1760_ = v_a_1691_;
                        state = 6;
                        continue;
                    }
                    2 => {
                        crate::leanh::lean_dec_ref(v_defaultPkg_1682_);
                        v_toContext_1773_ = crate::leanh::lean_ctor_get(v_a_1690_, 1);
                        v_packageMap_1774_ = crate::leanh::lean_ctor_get(v_toContext_1773_, 5);
                        v___x_1775_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_1774_, v_package_1737_);
                        if crate::leanh::lean_obj_tag(v___x_1775_) == 1 {
                            crate::leanh::lean_dec_ref_known(v_package_1737_, 2);
                            crate::leanh::lean_dec_ref(v_root_1683_);
                            v_val_1776_ = crate::leanh::lean_ctor_get(v___x_1775_, 0);
                            crate::leanh::lean_inc(v_val_1776_);
                            crate::leanh::lean_dec_ref_known(v___x_1775_, 1);
                            v_a_1759_ = v_val_1776_;
                            v_a_1760_ = v_a_1691_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1775_);
                            crate::leanh::lean_del_object(v___x_1739_);
                            v___x_1777_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                            v___x_1778_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                            v___x_1779_ = lean_string_append(v___x_1777_, v___x_1778_);
                            crate::leanh::lean_dec_ref(v___x_1778_);
                            v___x_1780_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                            v___x_1781_ = lean_string_append(v___x_1779_, v___x_1780_);
                            v___x_1782_ = 1;
                            v___x_1783_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_package_1737_,
                                    v___x_1782_,
                                );
                            v___x_1784_ = lean_string_append(v___x_1781_, v___x_1783_);
                            crate::leanh::lean_dec_ref(v___x_1783_);
                            v___x_1785_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                            v___x_1786_ = lean_string_append(v___x_1784_, v___x_1785_);
                            v___x_1787_ = 3;
                            v___x_1788_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_1788_, 0, v___x_1786_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_1788_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_1787_,
                            );
                            v___x_1789_ = lean_array_get_size(v_a_1691_);
                            v___x_1790_ = lean_array_push(v_a_1691_, v___x_1788_);
                            v_a_1702_ = v___x_1789_;
                            v_a_1703_ = v___x_1790_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v_defaultPkg_1682_);
                        v_toContext_1791_ = crate::leanh::lean_ctor_get(v_a_1690_, 1);
                        v_packages_1792_ = crate::leanh::lean_ctor_get(v_toContext_1791_, 4);
                        v___x_1793_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                        v_sz_1794_ = lean_array_size(v_packages_1792_);
                        v___x_1795_ = 0usize;
                        v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_1737_, v_packages_1792_, v_sz_1794_, v___x_1795_, v___x_1793_);
                        v_fst_1797_ = crate::leanh::lean_ctor_get(v___x_1796_, 0);
                        crate::leanh::lean_inc(v_fst_1797_);
                        crate::leanh::lean_dec_ref(v___x_1796_);
                        if crate::leanh::lean_obj_tag(v_fst_1797_) == 0 {
                            crate::leanh::lean_del_object(v___x_1739_);
                            v_a_1742_ = v_a_1691_;
                            state = 5;
                            continue;
                        } else {
                            v_val_1798_ = crate::leanh::lean_ctor_get(v_fst_1797_, 0);
                            crate::leanh::lean_inc(v_val_1798_);
                            crate::leanh::lean_dec_ref_known(v_fst_1797_, 1);
                            if crate::leanh::lean_obj_tag(v_val_1798_) == 1 {
                                crate::leanh::lean_dec(v_package_1737_);
                                crate::leanh::lean_dec_ref(v_root_1683_);
                                v_val_1799_ = crate::leanh::lean_ctor_get(v_val_1798_, 0);
                                crate::leanh::lean_inc(v_val_1799_);
                                crate::leanh::lean_dec_ref_known(v_val_1798_, 1);
                                v_a_1759_ = v_val_1799_;
                                v_a_1760_ = v_a_1691_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_val_1798_);
                                crate::leanh::lean_del_object(v___x_1739_);
                                v_a_1742_ = v_a_1691_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            5 => {
                v___x_1743_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                v___x_1744_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                v___x_1745_ = lean_string_append(v___x_1743_, v___x_1744_);
                crate::leanh::lean_dec_ref(v___x_1744_);
                v___x_1746_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                v___x_1747_ = lean_string_append(v___x_1745_, v___x_1746_);
                v___x_1748_ = 1;
                v___x_1749_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_package_1737_,
                    v___x_1748_,
                );
                v___x_1750_ = lean_string_append(v___x_1747_, v___x_1749_);
                crate::leanh::lean_dec_ref(v___x_1749_);
                v___x_1751_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                v___x_1752_ = lean_string_append(v___x_1750_, v___x_1751_);
                v___x_1753_ = 3;
                v___x_1754_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1754_, 0, v___x_1752_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1754_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1753_,
                );
                v___x_1755_ = lean_array_get_size(v_a_1742_);
                v___x_1756_ = lean_array_push(v_a_1742_, v___x_1754_);
                v_a_1702_ = v___x_1755_;
                v_a_1703_ = v___x_1756_;
                state = 3;
                continue;
            }
            6 => {
                v_keyName_1761_ = crate::leanh::lean_ctor_get(v_a_1759_, 2);
                crate::leanh::lean_inc(v_keyName_1761_);
                if v_isShared_1740_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1739_, 0, v_keyName_1761_);
                    v___x_1763_ = v___x_1739_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_keyName_1761_);
                    v___x_1763_ = v_reuseFailAlloc_1772_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1764_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                v___x_1765_ = 0;
                v___x_1766_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                v___x_1767_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1767_, 0, v_a_1759_);
                crate::leanh::lean_ctor_set(v___x_1767_, 1, v___x_1766_);
                v___x_1768_ = lean_task_pure(v___x_1767_);
                v___x_1769_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1769_, 0, v___x_1768_);
                crate::leanh::lean_ctor_set(v___x_1769_, 1, v___x_1757_);
                crate::leanh::lean_ctor_set(v___x_1769_, 2, v___x_1764_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1769_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1765_,
                );
                v___x_1770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1770_, 0, v___x_1763_);
                crate::leanh::lean_ctor_set(v___x_1770_, 1, v___x_1769_);
                v___x_1771_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1771_, 0, v___x_1770_);
                crate::leanh::lean_ctor_set(v___x_1771_, 1, v_a_1760_);
                return v___x_1771_;
            }
            8 => match crate::leanh::lean_obj_tag(v_package_1801_) {
                0 => {
                    v_a_1807_ = v_defaultPkg_1682_;
                    v_a_1808_ = v_a_1691_;
                    state = 9;
                    continue;
                }
                2 => {
                    crate::leanh::lean_dec_ref(v_defaultPkg_1682_);
                    v_toContext_1860_ = crate::leanh::lean_ctor_get(v_a_1690_, 1);
                    v_packageMap_1861_ = crate::leanh::lean_ctor_get(v_toContext_1860_, 5);
                    v___x_1862_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_1861_, v_package_1801_);
                    if crate::leanh::lean_obj_tag(v___x_1862_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_package_1801_, 2);
                        v_val_1863_ = crate::leanh::lean_ctor_get(v___x_1862_, 0);
                        crate::leanh::lean_inc(v_val_1863_);
                        crate::leanh::lean_dec_ref_known(v___x_1862_, 1);
                        v_a_1807_ = v_val_1863_;
                        v_a_1808_ = v_a_1691_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1862_);
                        crate::leanh::lean_del_object(v___x_1804_);
                        crate::leanh::lean_dec(v_module_1802_);
                        v___x_1864_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_1865_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                        v___x_1866_ = lean_string_append(v___x_1864_, v___x_1865_);
                        crate::leanh::lean_dec_ref(v___x_1865_);
                        v___x_1867_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                        v___x_1868_ = lean_string_append(v___x_1866_, v___x_1867_);
                        v___x_1869_ = 1;
                        v___x_1870_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_package_1801_,
                                v___x_1869_,
                            );
                        v___x_1871_ = lean_string_append(v___x_1868_, v___x_1870_);
                        crate::leanh::lean_dec_ref(v___x_1870_);
                        v___x_1872_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                        v___x_1873_ = lean_string_append(v___x_1871_, v___x_1872_);
                        v___x_1874_ = 3;
                        v___x_1875_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1875_, 0, v___x_1873_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1875_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1874_,
                        );
                        v___x_1876_ = lean_array_get_size(v_a_1691_);
                        v___x_1877_ = lean_array_push(v_a_1691_, v___x_1875_);
                        v_a_1698_ = v___x_1876_;
                        v_a_1699_ = v___x_1877_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_defaultPkg_1682_);
                    v_toContext_1878_ = crate::leanh::lean_ctor_get(v_a_1690_, 1);
                    v_packages_1879_ = crate::leanh::lean_ctor_get(v_toContext_1878_, 4);
                    v___x_1880_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                    v_sz_1881_ = lean_array_size(v_packages_1879_);
                    v___x_1882_ = 0usize;
                    v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_1801_, v_packages_1879_, v_sz_1881_, v___x_1882_, v___x_1880_);
                    v_fst_1884_ = crate::leanh::lean_ctor_get(v___x_1883_, 0);
                    crate::leanh::lean_inc(v_fst_1884_);
                    crate::leanh::lean_dec_ref(v___x_1883_);
                    if crate::leanh::lean_obj_tag(v_fst_1884_) == 0 {
                        crate::leanh::lean_del_object(v___x_1804_);
                        crate::leanh::lean_dec(v_module_1802_);
                        v_a_1845_ = v_a_1691_;
                        state = 11;
                        continue;
                    } else {
                        v_val_1885_ = crate::leanh::lean_ctor_get(v_fst_1884_, 0);
                        crate::leanh::lean_inc(v_val_1885_);
                        crate::leanh::lean_dec_ref_known(v_fst_1884_, 1);
                        if crate::leanh::lean_obj_tag(v_val_1885_) == 1 {
                            crate::leanh::lean_dec(v_package_1801_);
                            v_val_1886_ = crate::leanh::lean_ctor_get(v_val_1885_, 0);
                            crate::leanh::lean_inc(v_val_1886_);
                            crate::leanh::lean_dec_ref_known(v_val_1885_, 1);
                            v_a_1807_ = v_val_1886_;
                            v_a_1808_ = v_a_1691_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_1885_);
                            crate::leanh::lean_del_object(v___x_1804_);
                            crate::leanh::lean_dec(v_module_1802_);
                            v_a_1845_ = v_a_1691_;
                            state = 11;
                            continue;
                        }
                    }
                }
            },
            9 => {
                crate::leanh::lean_inc_ref(v_a_1807_);
                crate::leanh::lean_inc(v_module_1802_);
                v___x_1809_ = l_Lake_Package_findTargetModule_x3f(v_module_1802_, v_a_1807_);
                if crate::leanh::lean_obj_tag(v___x_1809_) == 1 {
                    crate::leanh::lean_dec_ref(v_root_1683_);
                    v_val_1810_ = crate::leanh::lean_ctor_get(v___x_1809_, 0);
                    crate::leanh::lean_inc(v_val_1810_);
                    crate::leanh::lean_dec_ref_known(v___x_1809_, 1);
                    v_keyName_1811_ = crate::leanh::lean_ctor_get(v_a_1807_, 2);
                    crate::leanh::lean_inc(v_keyName_1811_);
                    crate::leanh::lean_dec_ref(v_a_1807_);
                    if v_isShared_1805_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1804_, 0, v_keyName_1811_);
                        v___x_1813_ = v___x_1804_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1822_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_keyName_1811_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_module_1802_);
                        v___x_1813_ = v_reuseFailAlloc_1822_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1809_);
                    crate::leanh::lean_del_object(v___x_1804_);
                    v_baseName_1823_ = crate::leanh::lean_ctor_get(v_a_1807_, 1);
                    crate::leanh::lean_inc(v_baseName_1823_);
                    crate::leanh::lean_dec_ref(v_a_1807_);
                    v___x_1824_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_1825_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                    v___x_1826_ = lean_string_append(v___x_1824_, v___x_1825_);
                    crate::leanh::lean_dec_ref(v___x_1825_);
                    v___x_1827_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6;
                    v___x_1828_ = lean_string_append(v___x_1826_, v___x_1827_);
                    v___x_1829_ = 1;
                    v___x_1830_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_module_1802_,
                        v___x_1829_,
                    );
                    v___x_1831_ = lean_string_append(v___x_1828_, v___x_1830_);
                    crate::leanh::lean_dec_ref(v___x_1830_);
                    v___x_1832_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7;
                    v___x_1833_ = lean_string_append(v___x_1831_, v___x_1832_);
                    v___x_1834_ = 0;
                    v___x_1835_ = l_Lean_Name_toString(v_baseName_1823_, v___x_1834_);
                    v___x_1836_ = lean_string_append(v___x_1833_, v___x_1835_);
                    crate::leanh::lean_dec_ref(v___x_1835_);
                    v___x_1837_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                    v___x_1838_ = lean_string_append(v___x_1836_, v___x_1837_);
                    v___x_1839_ = 3;
                    v___x_1840_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1840_, 0, v___x_1838_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1840_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_1839_,
                    );
                    v___x_1841_ = lean_array_get_size(v_a_1808_);
                    v___x_1842_ = lean_array_push(v_a_1808_, v___x_1840_);
                    v___x_1843_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1843_, 0, v___x_1841_);
                    crate::leanh::lean_ctor_set(v___x_1843_, 1, v___x_1842_);
                    return v___x_1843_;
                }
            }
            10 => {
                v___x_1814_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                v___x_1815_ = 0;
                v___x_1816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                v___x_1817_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1817_, 0, v_val_1810_);
                crate::leanh::lean_ctor_set(v___x_1817_, 1, v___x_1816_);
                v___x_1818_ = lean_task_pure(v___x_1817_);
                v___x_1819_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1819_, 0, v___x_1818_);
                crate::leanh::lean_ctor_set(v___x_1819_, 1, v___x_1705_);
                crate::leanh::lean_ctor_set(v___x_1819_, 2, v___x_1814_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1819_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1815_,
                );
                v___x_1820_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1820_, 0, v___x_1813_);
                crate::leanh::lean_ctor_set(v___x_1820_, 1, v___x_1819_);
                v___x_1821_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1821_, 0, v___x_1820_);
                crate::leanh::lean_ctor_set(v___x_1821_, 1, v_a_1808_);
                return v___x_1821_;
            }
            11 => {
                v___x_1846_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                v___x_1847_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                v___x_1848_ = lean_string_append(v___x_1846_, v___x_1847_);
                crate::leanh::lean_dec_ref(v___x_1847_);
                v___x_1849_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                v___x_1850_ = lean_string_append(v___x_1848_, v___x_1849_);
                v___x_1851_ = 1;
                v___x_1852_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_package_1801_,
                    v___x_1851_,
                );
                v___x_1853_ = lean_string_append(v___x_1850_, v___x_1852_);
                crate::leanh::lean_dec_ref(v___x_1852_);
                v___x_1854_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                v___x_1855_ = lean_string_append(v___x_1853_, v___x_1854_);
                v___x_1856_ = 3;
                v___x_1857_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1857_, 0, v___x_1855_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1857_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1856_,
                );
                v___x_1858_ = lean_array_get_size(v_a_1845_);
                v___x_1859_ = lean_array_push(v_a_1845_, v___x_1857_);
                v_a_1698_ = v___x_1858_;
                v_a_1699_ = v___x_1859_;
                state = 2;
                continue;
            }
            12 => match crate::leanh::lean_obj_tag(v_package_1888_) {
                0 => {
                    v_a_1894_ = v_defaultPkg_1682_;
                    v_a_1895_ = v_a_1691_;
                    state = 13;
                    continue;
                }
                2 => {
                    crate::leanh::lean_dec_ref(v_defaultPkg_1682_);
                    v_toContext_2012_ = crate::leanh::lean_ctor_get(v_a_1690_, 1);
                    v_packageMap_2013_ = crate::leanh::lean_ctor_get(v_toContext_2012_, 5);
                    v___x_2014_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_2013_, v_package_1888_);
                    if crate::leanh::lean_obj_tag(v___x_2014_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_package_1888_, 2);
                        v_val_2015_ = crate::leanh::lean_ctor_get(v___x_2014_, 0);
                        crate::leanh::lean_inc(v_val_2015_);
                        crate::leanh::lean_dec_ref_known(v___x_2014_, 1);
                        v_a_1894_ = v_val_2015_;
                        v_a_1895_ = v_a_1691_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2014_);
                        crate::leanh::lean_del_object(v___x_1891_);
                        crate::leanh::lean_dec(v_target_1889_);
                        crate::leanh::lean_dec_ref(v_a_1686_);
                        v___x_2016_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_2017_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                        v___x_2018_ = lean_string_append(v___x_2016_, v___x_2017_);
                        crate::leanh::lean_dec_ref(v___x_2017_);
                        v___x_2019_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                        v___x_2020_ = lean_string_append(v___x_2018_, v___x_2019_);
                        v___x_2021_ = 1;
                        v___x_2022_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_package_1888_,
                                v___x_2021_,
                            );
                        v___x_2023_ = lean_string_append(v___x_2020_, v___x_2022_);
                        crate::leanh::lean_dec_ref(v___x_2022_);
                        v___x_2024_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                        v___x_2025_ = lean_string_append(v___x_2023_, v___x_2024_);
                        v___x_2026_ = 3;
                        v___x_2027_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2027_, 0, v___x_2025_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2027_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2026_,
                        );
                        v___x_2028_ = lean_array_get_size(v_a_1691_);
                        v___x_2029_ = lean_array_push(v_a_1691_, v___x_2027_);
                        v_a_1694_ = v___x_2028_;
                        v_a_1695_ = v___x_2029_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_defaultPkg_1682_);
                    v_toContext_2030_ = crate::leanh::lean_ctor_get(v_a_1690_, 1);
                    v_packages_2031_ = crate::leanh::lean_ctor_get(v_toContext_2030_, 4);
                    v___x_2032_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                    v_sz_2033_ = lean_array_size(v_packages_2031_);
                    v___x_2034_ = 0usize;
                    v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_1888_, v_packages_2031_, v_sz_2033_, v___x_2034_, v___x_2032_);
                    v_fst_2036_ = crate::leanh::lean_ctor_get(v___x_2035_, 0);
                    crate::leanh::lean_inc(v_fst_2036_);
                    crate::leanh::lean_dec_ref(v___x_2035_);
                    if crate::leanh::lean_obj_tag(v_fst_2036_) == 0 {
                        crate::leanh::lean_del_object(v___x_1891_);
                        crate::leanh::lean_dec(v_target_1889_);
                        crate::leanh::lean_dec_ref(v_a_1686_);
                        v_a_1997_ = v_a_1691_;
                        state = 29;
                        continue;
                    } else {
                        v_val_2037_ = crate::leanh::lean_ctor_get(v_fst_2036_, 0);
                        crate::leanh::lean_inc(v_val_2037_);
                        crate::leanh::lean_dec_ref_known(v_fst_2036_, 1);
                        if crate::leanh::lean_obj_tag(v_val_2037_) == 1 {
                            crate::leanh::lean_dec(v_package_1888_);
                            v_val_2038_ = crate::leanh::lean_ctor_get(v_val_2037_, 0);
                            crate::leanh::lean_inc(v_val_2038_);
                            crate::leanh::lean_dec_ref_known(v_val_2037_, 1);
                            v_a_1894_ = v_val_2038_;
                            v_a_1895_ = v_a_1691_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_2037_);
                            crate::leanh::lean_del_object(v___x_1891_);
                            crate::leanh::lean_dec(v_target_1889_);
                            crate::leanh::lean_dec_ref(v_a_1686_);
                            v_a_1997_ = v_a_1691_;
                            state = 29;
                            continue;
                        }
                    }
                }
            },
            13 => {
                v_baseName_1896_ = crate::leanh::lean_ctor_get(v_a_1894_, 1);
                v_keyName_1897_ = crate::leanh::lean_ctor_get(v_a_1894_, 2);
                crate::leanh::lean_inc(v_target_1889_);
                crate::leanh::lean_inc(v_keyName_1897_);
                if v_isShared_1892_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1891_, 0, v_keyName_1897_);
                    v___x_1899_ = v___x_1891_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1995_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_keyName_1897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_target_1889_);
                    v___x_1899_ = v_reuseFailAlloc_1995_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_facetless_1685_ == 0 {
                    crate::leanh::lean_dec_ref(v_root_1683_);
                    v___x_1900_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1900_, 0, v_a_1894_);
                    crate::leanh::lean_ctor_set(v___x_1900_, 1, v_target_1889_);
                    crate::leanh::lean_inc_ref(v_a_1690_);
                    crate::leanh::lean_inc(v_a_1689_);
                    crate::leanh::lean_inc(v_a_1688_);
                    crate::leanh::lean_inc(v_a_1687_);
                    v___x_1901_ = crate::leanh::lean_apply_7(
                        v_a_1686_,
                        v___x_1900_,
                        v_a_1687_,
                        v_a_1688_,
                        v_a_1689_,
                        v_a_1690_,
                        v_a_1895_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1901_) == 0 {
                        v_a_1902_ = crate::leanh::lean_ctor_get(v___x_1901_, 0);
                        v_a_1903_ = crate::leanh::lean_ctor_get(v___x_1901_, 1);
                        v_isSharedCheck_1911_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1901_)) as u8;
                        if v_isSharedCheck_1911_ == 0 {
                            v___x_1905_ = v___x_1901_;
                            v_isShared_1906_ = v_isSharedCheck_1911_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1903_);
                            crate::leanh::lean_inc(v_a_1902_);
                            crate::leanh::lean_dec(v___x_1901_);
                            v___x_1905_ = crate::leanh::lean_box(0);
                            v_isShared_1906_ = v_isSharedCheck_1911_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1899_);
                        v_a_1912_ = crate::leanh::lean_ctor_get(v___x_1901_, 0);
                        v_a_1913_ = crate::leanh::lean_ctor_get(v___x_1901_, 1);
                        v_isSharedCheck_1920_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1901_)) as u8;
                        if v_isSharedCheck_1920_ == 0 {
                            v___x_1915_ = v___x_1901_;
                            v_isShared_1916_ = v_isSharedCheck_1920_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1913_);
                            crate::leanh::lean_inc(v_a_1912_);
                            crate::leanh::lean_dec(v___x_1901_);
                            v___x_1915_ = crate::leanh::lean_box(0);
                            v_isShared_1916_ = v_isSharedCheck_1920_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    v___x_1921_ = l_Lake_Package_findTargetDecl_x3f(v_target_1889_, v_a_1894_);
                    if crate::leanh::lean_obj_tag(v___x_1921_) == 1 {
                        crate::leanh::lean_dec_ref(v_root_1683_);
                        v_val_1922_ = crate::leanh::lean_ctor_get(v___x_1921_, 0);
                        crate::leanh::lean_inc(v_val_1922_);
                        crate::leanh::lean_dec_ref_known(v___x_1921_, 1);
                        v_name_1923_ = crate::leanh::lean_ctor_get(v_val_1922_, 1);
                        v_kind_1924_ = crate::leanh::lean_ctor_get(v_val_1922_, 2);
                        v_config_1925_ = crate::leanh::lean_ctor_get(v_val_1922_, 3);
                        v_isSharedCheck_1978_ =
                            (!crate::leanh::lean_is_exclusive(v_val_1922_)) as u8;
                        if v_isSharedCheck_1978_ == 0 {
                            v_unused_1979_ = crate::leanh::lean_ctor_get(v_val_1922_, 0);
                            crate::leanh::lean_dec(v_unused_1979_);
                            v___x_1927_ = v_val_1922_;
                            v_isShared_1928_ = v_isSharedCheck_1978_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_config_1925_);
                            crate::leanh::lean_inc(v_kind_1924_);
                            crate::leanh::lean_inc(v_name_1923_);
                            crate::leanh::lean_dec(v_val_1922_);
                            v___x_1927_ = crate::leanh::lean_box(0);
                            v_isShared_1928_ = v_isSharedCheck_1978_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_baseName_1896_);
                        crate::leanh::lean_dec(v___x_1921_);
                        crate::leanh::lean_dec_ref(v___x_1899_);
                        crate::leanh::lean_dec_ref(v_a_1894_);
                        crate::leanh::lean_dec(v_target_1889_);
                        crate::leanh::lean_dec_ref(v_a_1686_);
                        v___x_1980_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_1981_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                        v___x_1982_ = lean_string_append(v___x_1980_, v___x_1981_);
                        crate::leanh::lean_dec_ref(v___x_1981_);
                        v___x_1983_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10;
                        v___x_1984_ = lean_string_append(v___x_1982_, v___x_1983_);
                        v___x_1985_ = 0;
                        v___x_1986_ = l_Lean_Name_toString(v_baseName_1896_, v___x_1985_);
                        v___x_1987_ = lean_string_append(v___x_1984_, v___x_1986_);
                        crate::leanh::lean_dec_ref(v___x_1986_);
                        v___x_1988_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                        v___x_1989_ = lean_string_append(v___x_1987_, v___x_1988_);
                        v___x_1990_ = 3;
                        v___x_1991_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_1991_, 0, v___x_1989_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_1991_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_1990_,
                        );
                        v___x_1992_ = lean_array_get_size(v_a_1895_);
                        v___x_1993_ = lean_array_push(v_a_1895_, v___x_1991_);
                        v___x_1994_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1994_, 0, v___x_1992_);
                        crate::leanh::lean_ctor_set(v___x_1994_, 1, v___x_1993_);
                        return v___x_1994_;
                    }
                }
            }
            15 => {
                v___x_1907_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1907_, 0, v___x_1899_);
                crate::leanh::lean_ctor_set(v___x_1907_, 1, v_a_1902_);
                if v_isShared_1906_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1907_);
                    v___x_1909_ = v___x_1905_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1910_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_a_1903_);
                    v___x_1909_ = v_reuseFailAlloc_1910_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1909_;
            }
            17 => {
                if v_isShared_1916_ == 0 {
                    v___x_1918_ = v___x_1915_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1919_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_a_1913_);
                    v___x_1918_ = v_reuseFailAlloc_1919_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1918_;
            }
            19 => {
                v___x_1929_ = l_Lean_Name_isAnonymous(v_kind_1924_);
                if v___x_1929_ == 0 {
                    crate::leanh::lean_dec(v_target_1889_);
                    v___x_1930_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9;
                    crate::leanh::lean_inc(v_kind_1924_);
                    v___x_1931_ = l_Lean_Name_str___override(v_kind_1924_, v___x_1930_);
                    v___x_1932_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1932_, 0, v_a_1894_);
                    crate::leanh::lean_ctor_set(v___x_1932_, 1, v_name_1923_);
                    crate::leanh::lean_ctor_set(v___x_1932_, 2, v_config_1925_);
                    crate::leanh::lean_inc(v___x_1931_);
                    crate::leanh::lean_inc_ref(v___x_1899_);
                    if v_isShared_1928_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1927_, 1);
                        crate::leanh::lean_ctor_set(v___x_1927_, 3, v___x_1931_);
                        crate::leanh::lean_ctor_set(v___x_1927_, 2, v___x_1932_);
                        crate::leanh::lean_ctor_set(v___x_1927_, 1, v_kind_1924_);
                        crate::leanh::lean_ctor_set(v___x_1927_, 0, v___x_1899_);
                        v___x_1934_ = v___x_1927_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1956_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1899_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_kind_1924_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 2, v___x_1932_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 3, v___x_1931_);
                        v___x_1934_ = v_reuseFailAlloc_1956_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1927_);
                    crate::leanh::lean_dec(v_config_1925_);
                    crate::leanh::lean_dec(v_kind_1924_);
                    crate::leanh::lean_dec(v_name_1923_);
                    v___x_1957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1957_, 0, v_a_1894_);
                    crate::leanh::lean_ctor_set(v___x_1957_, 1, v_target_1889_);
                    crate::leanh::lean_inc_ref(v_a_1690_);
                    crate::leanh::lean_inc(v_a_1689_);
                    crate::leanh::lean_inc(v_a_1688_);
                    crate::leanh::lean_inc(v_a_1687_);
                    v___x_1958_ = crate::leanh::lean_apply_7(
                        v_a_1686_,
                        v___x_1957_,
                        v_a_1687_,
                        v_a_1688_,
                        v_a_1689_,
                        v_a_1690_,
                        v_a_1895_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_1958_) == 0 {
                        v_a_1959_ = crate::leanh::lean_ctor_get(v___x_1958_, 0);
                        v_a_1960_ = crate::leanh::lean_ctor_get(v___x_1958_, 1);
                        v_isSharedCheck_1968_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1958_)) as u8;
                        if v_isSharedCheck_1968_ == 0 {
                            v___x_1962_ = v___x_1958_;
                            v_isShared_1963_ = v_isSharedCheck_1968_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1960_);
                            crate::leanh::lean_inc(v_a_1959_);
                            crate::leanh::lean_dec(v___x_1958_);
                            v___x_1962_ = crate::leanh::lean_box(0);
                            v_isShared_1963_ = v_isSharedCheck_1968_;
                            state = 25;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1899_);
                        v_a_1969_ = crate::leanh::lean_ctor_get(v___x_1958_, 0);
                        v_a_1970_ = crate::leanh::lean_ctor_get(v___x_1958_, 1);
                        v_isSharedCheck_1977_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1958_)) as u8;
                        if v_isSharedCheck_1977_ == 0 {
                            v___x_1972_ = v___x_1958_;
                            v_isShared_1973_ = v_isSharedCheck_1977_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1970_);
                            crate::leanh::lean_inc(v_a_1969_);
                            crate::leanh::lean_dec(v___x_1958_);
                            v___x_1972_ = crate::leanh::lean_box(0);
                            v_isShared_1973_ = v_isSharedCheck_1977_;
                            state = 27;
                            continue;
                        }
                    }
                }
            }
            20 => {
                crate::leanh::lean_inc_ref(v_a_1690_);
                crate::leanh::lean_inc(v_a_1689_);
                crate::leanh::lean_inc(v_a_1688_);
                crate::leanh::lean_inc(v_a_1687_);
                v___x_1935_ = crate::leanh::lean_apply_7(
                    v_a_1686_,
                    v___x_1934_,
                    v_a_1687_,
                    v_a_1688_,
                    v_a_1689_,
                    v_a_1690_,
                    v_a_1895_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1935_) == 0 {
                    v_a_1936_ = crate::leanh::lean_ctor_get(v___x_1935_, 0);
                    v_a_1937_ = crate::leanh::lean_ctor_get(v___x_1935_, 1);
                    v_isSharedCheck_1946_ = (!crate::leanh::lean_is_exclusive(v___x_1935_)) as u8;
                    if v_isSharedCheck_1946_ == 0 {
                        v___x_1939_ = v___x_1935_;
                        v_isShared_1940_ = v_isSharedCheck_1946_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1937_);
                        crate::leanh::lean_inc(v_a_1936_);
                        crate::leanh::lean_dec(v___x_1935_);
                        v___x_1939_ = crate::leanh::lean_box(0);
                        v_isShared_1940_ = v_isSharedCheck_1946_;
                        state = 21;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1931_);
                    crate::leanh::lean_dec_ref(v___x_1899_);
                    v_a_1947_ = crate::leanh::lean_ctor_get(v___x_1935_, 0);
                    v_a_1948_ = crate::leanh::lean_ctor_get(v___x_1935_, 1);
                    v_isSharedCheck_1955_ = (!crate::leanh::lean_is_exclusive(v___x_1935_)) as u8;
                    if v_isSharedCheck_1955_ == 0 {
                        v___x_1950_ = v___x_1935_;
                        v_isShared_1951_ = v_isSharedCheck_1955_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1948_);
                        crate::leanh::lean_inc(v_a_1947_);
                        crate::leanh::lean_dec(v___x_1935_);
                        v___x_1950_ = crate::leanh::lean_box(0);
                        v_isShared_1951_ = v_isSharedCheck_1955_;
                        state = 23;
                        continue;
                    }
                }
            }
            21 => {
                v___x_1941_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1941_, 0, v___x_1899_);
                crate::leanh::lean_ctor_set(v___x_1941_, 1, v___x_1931_);
                v___x_1942_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1942_, 0, v___x_1941_);
                crate::leanh::lean_ctor_set(v___x_1942_, 1, v_a_1936_);
                if v_isShared_1940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1939_, 0, v___x_1942_);
                    v___x_1944_ = v___x_1939_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_a_1937_);
                    v___x_1944_ = v_reuseFailAlloc_1945_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1944_;
            }
            23 => {
                if v_isShared_1951_ == 0 {
                    v___x_1953_ = v___x_1950_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1954_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_a_1948_);
                    v___x_1953_ = v_reuseFailAlloc_1954_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1953_;
            }
            25 => {
                v___x_1964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1964_, 0, v___x_1899_);
                crate::leanh::lean_ctor_set(v___x_1964_, 1, v_a_1959_);
                if v_isShared_1963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1962_, 0, v___x_1964_);
                    v___x_1966_ = v___x_1962_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1967_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_a_1960_);
                    v___x_1966_ = v_reuseFailAlloc_1967_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1966_;
            }
            27 => {
                if v_isShared_1973_ == 0 {
                    v___x_1975_ = v___x_1972_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1976_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_a_1970_);
                    v___x_1975_ = v_reuseFailAlloc_1976_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1975_;
            }
            29 => {
                v___x_1998_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                v___x_1999_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                v___x_2000_ = lean_string_append(v___x_1998_, v___x_1999_);
                crate::leanh::lean_dec_ref(v___x_1999_);
                v___x_2001_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                v___x_2002_ = lean_string_append(v___x_2000_, v___x_2001_);
                v___x_2003_ = 1;
                v___x_2004_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_package_1888_,
                    v___x_2003_,
                );
                v___x_2005_ = lean_string_append(v___x_2002_, v___x_2004_);
                crate::leanh::lean_dec_ref(v___x_2004_);
                v___x_2006_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                v___x_2007_ = lean_string_append(v___x_2005_, v___x_2006_);
                v___x_2008_ = 3;
                v___x_2009_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2009_, 0, v___x_2007_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2009_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2008_,
                );
                v___x_2010_ = lean_array_get_size(v_a_1997_);
                v___x_2011_ = lean_array_push(v_a_1997_, v___x_2009_);
                v_a_1694_ = v___x_2010_;
                v_a_1695_ = v___x_2011_;
                state = 1;
                continue;
            }
            30 => {
                v___x_2045_ = 0;
                crate::leanh::lean_inc_ref(v_a_1686_);
                crate::leanh::lean_inc_ref(v_target_2040_);
                crate::leanh::lean_inc_ref(v_root_1683_);
                v___x_2046_ =
                    l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
                        v_defaultPkg_1682_,
                        v_root_1683_,
                        v_target_2040_,
                        v___x_2045_,
                        v_a_1686_,
                        v_a_1687_,
                        v_a_1688_,
                        v_a_1689_,
                        v_a_1690_,
                        v_a_1691_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2046_) == 0 {
                    v_a_2047_ = crate::leanh::lean_ctor_get(v___x_2046_, 0);
                    crate::leanh::lean_inc(v_a_2047_);
                    v_snd_2048_ = crate::leanh::lean_ctor_get(v_a_2047_, 1);
                    v_isSharedCheck_2110_ = (!crate::leanh::lean_is_exclusive(v_a_2047_)) as u8;
                    if v_isSharedCheck_2110_ == 0 {
                        v_unused_2111_ = crate::leanh::lean_ctor_get(v_a_2047_, 0);
                        crate::leanh::lean_dec(v_unused_2111_);
                        v___x_2050_ = v_a_2047_;
                        v_isShared_2051_ = v_isSharedCheck_2110_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2048_);
                        crate::leanh::lean_dec(v_a_2047_);
                        v___x_2050_ = crate::leanh::lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2110_;
                        state = 31;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2043_);
                    crate::leanh::lean_dec(v_facet_2041_);
                    crate::leanh::lean_dec_ref(v_target_2040_);
                    crate::leanh::lean_dec_ref(v_a_1686_);
                    crate::leanh::lean_dec_ref(v_root_1683_);
                    return v___x_2046_;
                }
            }
            31 => {
                v_a_2052_ = crate::leanh::lean_ctor_get(v___x_2046_, 1);
                v_isSharedCheck_2108_ = (!crate::leanh::lean_is_exclusive(v___x_2046_)) as u8;
                if v_isSharedCheck_2108_ == 0 {
                    v_unused_2109_ = crate::leanh::lean_ctor_get(v___x_2046_, 0);
                    crate::leanh::lean_dec(v_unused_2109_);
                    v___x_2054_ = v___x_2046_;
                    v_isShared_2055_ = v_isSharedCheck_2108_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2052_);
                    crate::leanh::lean_dec(v___x_2046_);
                    v___x_2054_ = crate::leanh::lean_box(0);
                    v_isShared_2055_ = v_isSharedCheck_2108_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v_kind_2056_ = crate::leanh::lean_ctor_get(v_snd_2048_, 1);
                v___x_2095_ = l_Lean_Name_isAnonymous(v_kind_2056_);
                if v___x_2095_ == 0 {
                    v___x_2096_ = l_Lean_Name_isAnonymous(v_facet_2041_);
                    if v___x_2096_ == 0 {
                        v___y_2058_ = v_facet_2041_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_facet_2041_);
                        v___x_2097_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12;
                        v___y_2058_ = v___x_2097_;
                        state = 33;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2054_);
                    crate::leanh::lean_del_object(v___x_2050_);
                    crate::leanh::lean_dec(v_snd_2048_);
                    crate::leanh::lean_del_object(v___x_2043_);
                    crate::leanh::lean_dec(v_facet_2041_);
                    crate::leanh::lean_dec_ref(v_target_2040_);
                    crate::leanh::lean_dec_ref(v_a_1686_);
                    v___x_2098_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_2099_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                    v___x_2100_ = lean_string_append(v___x_2098_, v___x_2099_);
                    crate::leanh::lean_dec_ref(v___x_2099_);
                    v___x_2101_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13;
                    v___x_2102_ = lean_string_append(v___x_2100_, v___x_2101_);
                    v___x_2103_ = 3;
                    v___x_2104_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2104_, 0, v___x_2102_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2104_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2103_,
                    );
                    v___x_2105_ = lean_array_get_size(v_a_2052_);
                    v___x_2106_ = lean_array_push(v_a_2052_, v___x_2104_);
                    v___x_2107_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2107_, 0, v___x_2105_);
                    crate::leanh::lean_ctor_set(v___x_2107_, 1, v___x_2106_);
                    return v___x_2107_;
                }
            }
            33 => {
                v_toContext_2059_ = crate::leanh::lean_ctor_get(v_a_1690_, 1);
                v_facetConfigs_2060_ = crate::leanh::lean_ctor_get(v_toContext_2059_, 6);
                crate::leanh::lean_inc(v_kind_2056_);
                v___x_2061_ = l_Lean_Name_append(v_kind_2056_, v___y_2058_);
                v___x_2062_ = l_Lake_FacetConfigMap_get_x3f(v___x_2061_, v_facetConfigs_2060_);
                if crate::leanh::lean_obj_tag(v___x_2062_) == 1 {
                    crate::leanh::lean_dec_ref(v_root_1683_);
                    v_val_2063_ = crate::leanh::lean_ctor_get(v___x_2062_, 0);
                    crate::leanh::lean_inc(v_val_2063_);
                    crate::leanh::lean_dec_ref_known(v___x_2062_, 1);
                    v_outKind_2064_ = crate::leanh::lean_ctor_get(v_val_2063_, 2);
                    crate::leanh::lean_inc(v_outKind_2064_);
                    crate::leanh::lean_dec(v_val_2063_);
                    crate::leanh::lean_inc(v___x_2061_);
                    crate::leanh::lean_inc(v_kind_2056_);
                    crate::leanh::lean_inc_ref(v_target_2040_);
                    v___f_2065_ = crate::leanh::lean_alloc_closure(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed as *mut core::ffi::c_void, 11, 3);
                    crate::leanh::lean_closure_set(v___f_2065_, 0, v_target_2040_);
                    crate::leanh::lean_closure_set(v___f_2065_, 1, v_kind_2056_);
                    crate::leanh::lean_closure_set(v___f_2065_, 2, v___x_2061_);
                    v___x_2066_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2067_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
                    v___x_2068_ = l_Lake_Job_bindM___redArg(
                        v_outKind_2064_,
                        v_snd_2048_,
                        v___f_2065_,
                        v___x_2066_,
                        v___x_2045_,
                        v_a_1686_,
                        v_a_1687_,
                        v_a_1688_,
                        v_a_1689_,
                        v_a_1690_,
                        v___x_2067_,
                    );
                    if v_isShared_2044_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2043_, 1, v___x_2061_);
                        v___x_2070_ = v___x_2043_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_target_2040_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2061_);
                        v___x_2070_ = v_reuseFailAlloc_2077_;
                        state = 34;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2062_);
                    crate::leanh::lean_del_object(v___x_2050_);
                    crate::leanh::lean_dec(v_snd_2048_);
                    crate::leanh::lean_del_object(v___x_2043_);
                    crate::leanh::lean_dec_ref(v_target_2040_);
                    crate::leanh::lean_dec_ref(v_a_1686_);
                    v___x_2078_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_2079_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                    v___x_2080_ = lean_string_append(v___x_2078_, v___x_2079_);
                    crate::leanh::lean_dec_ref(v___x_2079_);
                    v___x_2081_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11;
                    v___x_2082_ = lean_string_append(v___x_2080_, v___x_2081_);
                    v___x_2083_ = 1;
                    v___x_2084_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___x_2061_,
                        v___x_2083_,
                    );
                    v___x_2085_ = lean_string_append(v___x_2082_, v___x_2084_);
                    crate::leanh::lean_dec_ref(v___x_2084_);
                    v___x_2086_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                    v___x_2087_ = lean_string_append(v___x_2085_, v___x_2086_);
                    v___x_2088_ = 3;
                    v___x_2089_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2089_, 0, v___x_2087_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2089_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2088_,
                    );
                    v___x_2090_ = lean_array_get_size(v_a_2052_);
                    v___x_2091_ = lean_array_push(v_a_2052_, v___x_2089_);
                    if v_isShared_2055_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2054_, 1);
                        crate::leanh::lean_ctor_set(v___x_2054_, 1, v___x_2091_);
                        crate::leanh::lean_ctor_set(v___x_2054_, 0, v___x_2090_);
                        v___x_2093_ = v___x_2054_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_2094_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2090_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2091_);
                        v___x_2093_ = v_reuseFailAlloc_2094_;
                        state = 37;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_2051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2050_, 1, v___x_2068_);
                    crate::leanh::lean_ctor_set(v___x_2050_, 0, v___x_2070_);
                    v___x_2072_ = v___x_2050_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___x_2068_);
                    v___x_2072_ = v_reuseFailAlloc_2076_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_2055_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2054_, 0, v___x_2072_);
                    v___x_2074_ = v___x_2054_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2075_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_a_2052_);
                    v___x_2074_ = v_reuseFailAlloc_2075_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_2074_;
            }
            37 => {
                return v___x_2093_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___boxed(
    mut v_defaultPkg_2113_: *mut crate::leanh::LeanObject,
    mut v_root_2114_: *mut crate::leanh::LeanObject,
    mut v_self_2115_: *mut crate::leanh::LeanObject,
    mut v_facetless_2116_: *mut crate::leanh::LeanObject,
    mut v_a_2117_: *mut crate::leanh::LeanObject,
    mut v_a_2118_: *mut crate::leanh::LeanObject,
    mut v_a_2119_: *mut crate::leanh::LeanObject,
    mut v_a_2120_: *mut crate::leanh::LeanObject,
    mut v_a_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
    mut v_a_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_facetless_boxed_2124_: u8 = 0;
    let mut v_res_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_facetless_boxed_2124_ = (crate::leanh::lean_unbox(v_facetless_2116_) as u8);
    v_res_2125_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
        v_defaultPkg_2113_,
        v_root_2114_,
        v_self_2115_,
        v_facetless_boxed_2124_,
        v_a_2117_,
        v_a_2118_,
        v_a_2119_,
        v_a_2120_,
        v_a_2121_,
        v_a_2122_,
    );
    crate::leanh::lean_dec_ref(v_a_2121_);
    crate::leanh::lean_dec(v_a_2120_);
    crate::leanh::lean_dec(v_a_2119_);
    crate::leanh::lean_dec(v_a_2118_);
    return v_res_2125_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(
    mut v_00_u03b2_2126_: *mut crate::leanh::LeanObject,
    mut v_inst_2127_: *mut crate::leanh::LeanObject,
    mut v_t_2128_: *mut crate::leanh::LeanObject,
    mut v_k_2129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2130_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_t_2128_, v_k_2129_);
    return v___x_2130_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___boxed(
    mut v_00_u03b2_2131_: *mut crate::leanh::LeanObject,
    mut v_inst_2132_: *mut crate::leanh::LeanObject,
    mut v_t_2133_: *mut crate::leanh::LeanObject,
    mut v_k_2134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2135_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(v_00_u03b2_2131_, v_inst_2132_, v_t_2133_, v_k_2134_);
    crate::leanh::lean_dec(v_k_2134_);
    crate::leanh::lean_dec(v_t_2133_);
    return v_res_2135_;
}
pub unsafe fn l_Lake_PartialBuildKey_fetchInCore(
    mut v_defaultPkg_2136_: *mut crate::leanh::LeanObject,
    mut v_self_2137_: *mut crate::leanh::LeanObject,
    mut v_a_2138_: *mut crate::leanh::LeanObject,
    mut v_a_2139_: *mut crate::leanh::LeanObject,
    mut v_a_2140_: *mut crate::leanh::LeanObject,
    mut v_a_2141_: *mut crate::leanh::LeanObject,
    mut v_a_2142_: *mut crate::leanh::LeanObject,
    mut v_a_2143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2145_: u8 = 0;
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2145_ = 1;
    crate::leanh::lean_inc_ref(v_self_2137_);
    v___x_2146_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
        v_defaultPkg_2136_,
        v_self_2137_,
        v_self_2137_,
        v___x_2145_,
        v_a_2138_,
        v_a_2139_,
        v_a_2140_,
        v_a_2141_,
        v_a_2142_,
        v_a_2143_,
    );
    return v___x_2146_;
}
pub unsafe fn l_Lake_PartialBuildKey_fetchInCore___boxed(
    mut v_defaultPkg_2147_: *mut crate::leanh::LeanObject,
    mut v_self_2148_: *mut crate::leanh::LeanObject,
    mut v_a_2149_: *mut crate::leanh::LeanObject,
    mut v_a_2150_: *mut crate::leanh::LeanObject,
    mut v_a_2151_: *mut crate::leanh::LeanObject,
    mut v_a_2152_: *mut crate::leanh::LeanObject,
    mut v_a_2153_: *mut crate::leanh::LeanObject,
    mut v_a_2154_: *mut crate::leanh::LeanObject,
    mut v_a_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2156_ = l_Lake_PartialBuildKey_fetchInCore(
        v_defaultPkg_2147_,
        v_self_2148_,
        v_a_2149_,
        v_a_2150_,
        v_a_2151_,
        v_a_2152_,
        v_a_2153_,
        v_a_2154_,
    );
    crate::leanh::lean_dec_ref(v_a_2153_);
    crate::leanh::lean_dec(v_a_2152_);
    crate::leanh::lean_dec(v_a_2151_);
    crate::leanh::lean_dec(v_a_2150_);
    return v_res_2156_;
}
pub unsafe fn l_Lake_PartialBuildKey_fetchIn(
    mut v_defaultPkg_2157_: *mut crate::leanh::LeanObject,
    mut v_self_2158_: *mut crate::leanh::LeanObject,
    mut v_a_2159_: *mut crate::leanh::LeanObject,
    mut v_a_2160_: *mut crate::leanh::LeanObject,
    mut v_a_2161_: *mut crate::leanh::LeanObject,
    mut v_a_2162_: *mut crate::leanh::LeanObject,
    mut v_a_2163_: *mut crate::leanh::LeanObject,
    mut v_a_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2172_: u8 = 0;
    let mut v_snd_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2178_: u8 = 0;
    let mut v_a_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2166_ = 1;
                crate::leanh::lean_inc_ref(v_self_2158_);
                v___x_2167_ =
                    l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
                        v_defaultPkg_2157_,
                        v_self_2158_,
                        v_self_2158_,
                        v___x_2166_,
                        v_a_2159_,
                        v_a_2160_,
                        v_a_2161_,
                        v_a_2162_,
                        v_a_2163_,
                        v_a_2164_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2167_) == 0 {
                    v_a_2168_ = crate::leanh::lean_ctor_get(v___x_2167_, 0);
                    v_a_2169_ = crate::leanh::lean_ctor_get(v___x_2167_, 1);
                    v_isSharedCheck_2178_ = (!crate::leanh::lean_is_exclusive(v___x_2167_)) as u8;
                    if v_isSharedCheck_2178_ == 0 {
                        v___x_2171_ = v___x_2167_;
                        v_isShared_2172_ = v_isSharedCheck_2178_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2169_);
                        crate::leanh::lean_inc(v_a_2168_);
                        crate::leanh::lean_dec(v___x_2167_);
                        v___x_2171_ = crate::leanh::lean_box(0);
                        v_isShared_2172_ = v_isSharedCheck_2178_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2179_ = crate::leanh::lean_ctor_get(v___x_2167_, 0);
                    v_a_2180_ = crate::leanh::lean_ctor_get(v___x_2167_, 1);
                    v_isSharedCheck_2187_ = (!crate::leanh::lean_is_exclusive(v___x_2167_)) as u8;
                    if v_isSharedCheck_2187_ == 0 {
                        v___x_2182_ = v___x_2167_;
                        v_isShared_2183_ = v_isSharedCheck_2187_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2180_);
                        crate::leanh::lean_inc(v_a_2179_);
                        crate::leanh::lean_dec(v___x_2167_);
                        v___x_2182_ = crate::leanh::lean_box(0);
                        v_isShared_2183_ = v_isSharedCheck_2187_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2173_ = crate::leanh::lean_ctor_get(v_a_2168_, 1);
                crate::leanh::lean_inc(v_snd_2173_);
                crate::leanh::lean_dec(v_a_2168_);
                v___x_2174_ = l_Lake_Job_toOpaque___redArg(v_snd_2173_);
                if v_isShared_2172_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2171_, 0, v___x_2174_);
                    v___x_2176_ = v___x_2171_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_a_2169_);
                    v___x_2176_ = v_reuseFailAlloc_2177_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2176_;
            }
            3 => {
                if v_isShared_2183_ == 0 {
                    v___x_2185_ = v___x_2182_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2186_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_a_2180_);
                    v___x_2185_ = v_reuseFailAlloc_2186_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_PartialBuildKey_fetchIn___boxed(
    mut v_defaultPkg_2188_: *mut crate::leanh::LeanObject,
    mut v_self_2189_: *mut crate::leanh::LeanObject,
    mut v_a_2190_: *mut crate::leanh::LeanObject,
    mut v_a_2191_: *mut crate::leanh::LeanObject,
    mut v_a_2192_: *mut crate::leanh::LeanObject,
    mut v_a_2193_: *mut crate::leanh::LeanObject,
    mut v_a_2194_: *mut crate::leanh::LeanObject,
    mut v_a_2195_: *mut crate::leanh::LeanObject,
    mut v_a_2196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2197_ = l_Lake_PartialBuildKey_fetchIn(
        v_defaultPkg_2188_,
        v_self_2189_,
        v_a_2190_,
        v_a_2191_,
        v_a_2192_,
        v_a_2193_,
        v_a_2194_,
        v_a_2195_,
    );
    crate::leanh::lean_dec_ref(v_a_2194_);
    crate::leanh::lean_dec(v_a_2193_);
    crate::leanh::lean_dec(v_a_2192_);
    crate::leanh::lean_dec(v_a_2191_);
    return v_res_2197_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(
    mut v_target_2198_: *mut crate::leanh::LeanObject,
    mut v_kind_2199_: *mut crate::leanh::LeanObject,
    mut v_facet_2200_: *mut crate::leanh::LeanObject,
    mut v_data_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
    mut v___y_2206_: *mut crate::leanh::LeanObject,
    mut v___y_2207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_log_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_action_2210_: u8 = 0;
    let mut v_wantsRebuild_2211_: u8 = 0;
    let mut v_trace_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buildTime_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2230_: u8 = 0;
    let mut v_a_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2235_: u8 = 0;
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_2209_ = crate::leanh::lean_ctor_get(v___y_2207_, 0);
                v_action_2210_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_2211_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                );
                v_trace_2212_ = crate::leanh::lean_ctor_get(v___y_2207_, 1);
                v_buildTime_2213_ = crate::leanh::lean_ctor_get(v___y_2207_, 2);
                v_isSharedCheck_2243_ = (!crate::leanh::lean_is_exclusive(v___y_2207_)) as u8;
                if v_isSharedCheck_2243_ == 0 {
                    v___x_2215_ = v___y_2207_;
                    v_isShared_2216_ = v_isSharedCheck_2243_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buildTime_2213_);
                    crate::leanh::lean_inc(v_trace_2212_);
                    crate::leanh::lean_inc(v_log_2209_);
                    crate::leanh::lean_dec(v___y_2207_);
                    v___x_2215_ = crate::leanh::lean_box(0);
                    v_isShared_2216_ = v_isSharedCheck_2243_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2217_ = crate::leanh::lean_alloc_ctor(1, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2217_, 0, v_target_2198_);
                crate::leanh::lean_ctor_set(v___x_2217_, 1, v_kind_2199_);
                crate::leanh::lean_ctor_set(v___x_2217_, 2, v_data_2201_);
                crate::leanh::lean_ctor_set(v___x_2217_, 3, v_facet_2200_);
                crate::leanh::lean_inc_ref(v___y_2206_);
                crate::leanh::lean_inc(v___y_2205_);
                crate::leanh::lean_inc(v___y_2204_);
                crate::leanh::lean_inc(v___y_2203_);
                v___x_2218_ = crate::leanh::lean_apply_7(
                    v___y_2202_,
                    v___x_2217_,
                    v___y_2203_,
                    v___y_2204_,
                    v___y_2205_,
                    v___y_2206_,
                    v_log_2209_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2218_) == 0 {
                    v_a_2219_ = crate::leanh::lean_ctor_get(v___x_2218_, 0);
                    v_a_2220_ = crate::leanh::lean_ctor_get(v___x_2218_, 1);
                    v_isSharedCheck_2230_ = (!crate::leanh::lean_is_exclusive(v___x_2218_)) as u8;
                    if v_isSharedCheck_2230_ == 0 {
                        v___x_2222_ = v___x_2218_;
                        v_isShared_2223_ = v_isSharedCheck_2230_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2220_);
                        crate::leanh::lean_inc(v_a_2219_);
                        crate::leanh::lean_dec(v___x_2218_);
                        v___x_2222_ = crate::leanh::lean_box(0);
                        v_isShared_2223_ = v_isSharedCheck_2230_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2231_ = crate::leanh::lean_ctor_get(v___x_2218_, 0);
                    v_a_2232_ = crate::leanh::lean_ctor_get(v___x_2218_, 1);
                    v_isSharedCheck_2242_ = (!crate::leanh::lean_is_exclusive(v___x_2218_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2234_ = v___x_2218_;
                        v_isShared_2235_ = v_isSharedCheck_2242_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2232_);
                        crate::leanh::lean_inc(v_a_2231_);
                        crate::leanh::lean_dec(v___x_2218_);
                        v___x_2234_ = crate::leanh::lean_box(0);
                        v_isShared_2235_ = v_isSharedCheck_2242_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2215_, 0, v_a_2220_);
                    v___x_2225_ = v___x_2215_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2229_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_trace_2212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_buildTime_2213_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2229_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_2210_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2229_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_2211_,
                    );
                    v___x_2225_ = v_reuseFailAlloc_2229_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2223_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2222_, 1, v___x_2225_);
                    v___x_2227_ = v___x_2222_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2228_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2219_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 1, v___x_2225_);
                    v___x_2227_ = v_reuseFailAlloc_2228_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2227_;
            }
            5 => {
                if v_isShared_2216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2215_, 0, v_a_2232_);
                    v___x_2237_ = v___x_2215_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = crate::leanh::lean_alloc_ctor(0, 3, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_trace_2212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_buildTime_2213_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2241_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_action_2210_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2241_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_2211_,
                    );
                    v___x_2237_ = v_reuseFailAlloc_2241_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2235_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2234_, 1, v___x_2237_);
                    v___x_2239_ = v___x_2234_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2231_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2237_);
                    v___x_2239_ = v_reuseFailAlloc_2240_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed(
    mut v_target_2244_: *mut crate::leanh::LeanObject,
    mut v_kind_2245_: *mut crate::leanh::LeanObject,
    mut v_facet_2246_: *mut crate::leanh::LeanObject,
    mut v_data_2247_: *mut crate::leanh::LeanObject,
    mut v___y_2248_: *mut crate::leanh::LeanObject,
    mut v___y_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
    mut v___y_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2255_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(
        v_target_2244_,
        v_kind_2245_,
        v_facet_2246_,
        v_data_2247_,
        v___y_2248_,
        v___y_2249_,
        v___y_2250_,
        v___y_2251_,
        v___y_2252_,
        v___y_2253_,
    );
    crate::leanh::lean_dec_ref(v___y_2252_);
    crate::leanh::lean_dec(v___y_2251_);
    crate::leanh::lean_dec(v___y_2250_);
    crate::leanh::lean_dec(v___y_2249_);
    return v_res_2255_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(
    mut v_root_2256_: *mut crate::leanh::LeanObject,
    mut v_self_2257_: *mut crate::leanh::LeanObject,
    mut v_a_2258_: *mut crate::leanh::LeanObject,
    mut v_a_2259_: *mut crate::leanh::LeanObject,
    mut v_a_2260_: *mut crate::leanh::LeanObject,
    mut v_a_2261_: *mut crate::leanh::LeanObject,
    mut v_a_2262_: *mut crate::leanh::LeanObject,
    mut v_a_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: u8 = 0;
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_packageMap_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: u8 = 0;
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toContext_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2325_: u8 = 0;
    let mut v_packageMap_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_baseName_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: u8 = 0;
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: u8 = 0;
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u8 = 0;
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_toContext_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2386_: u8 = 0;
    let mut v_packageMap_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: u8 = 0;
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2411_: u8 = 0;
    let mut v_target_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v_kind_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v_toContext_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_outKind_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u8 = 0;
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: u8 = 0;
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2265_ = l_Lake_instDataKindModule;
                match crate::leanh::lean_obj_tag(v_self_2257_) {
                    0 => {
                        crate::leanh::lean_dec_ref(v_a_2258_);
                        v_module_2266_ = crate::leanh::lean_ctor_get(v_self_2257_, 0);
                        crate::leanh::lean_inc_n(v_module_2266_, 2);
                        crate::leanh::lean_dec_ref_known(v_self_2257_, 1);
                        v_toContext_2267_ = crate::leanh::lean_ctor_get(v_a_2262_, 1);
                        v___x_2268_ =
                            l_Lake_Workspace_findModule_x3f(v_module_2266_, v_toContext_2267_);
                        if crate::leanh::lean_obj_tag(v___x_2268_) == 1 {
                            crate::leanh::lean_dec(v_module_2266_);
                            crate::leanh::lean_dec_ref(v_root_2256_);
                            v_val_2269_ = crate::leanh::lean_ctor_get(v___x_2268_, 0);
                            crate::leanh::lean_inc(v_val_2269_);
                            crate::leanh::lean_dec_ref_known(v___x_2268_, 1);
                            v___x_2270_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                            v___x_2271_ = 0;
                            v___x_2272_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                            v___x_2273_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2273_, 0, v_val_2269_);
                            crate::leanh::lean_ctor_set(v___x_2273_, 1, v___x_2272_);
                            v___x_2274_ = lean_task_pure(v___x_2273_);
                            v___x_2275_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_2275_, 0, v___x_2274_);
                            crate::leanh::lean_ctor_set(v___x_2275_, 1, v___x_2265_);
                            crate::leanh::lean_ctor_set(v___x_2275_, 2, v___x_2270_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_2275_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                                v___x_2271_,
                            );
                            v___x_2276_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2276_, 0, v___x_2275_);
                            crate::leanh::lean_ctor_set(v___x_2276_, 1, v_a_2263_);
                            return v___x_2276_;
                        } else {
                            crate::leanh::lean_dec(v___x_2268_);
                            v___x_2277_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                            v___x_2278_ = l_Lake_BuildKey_toString(v_root_2256_);
                            v___x_2279_ = lean_string_append(v___x_2277_, v___x_2278_);
                            crate::leanh::lean_dec_ref(v___x_2278_);
                            v___x_2280_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5;
                            v___x_2281_ = lean_string_append(v___x_2279_, v___x_2280_);
                            v___x_2282_ = 1;
                            v___x_2283_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_module_2266_,
                                    v___x_2282_,
                                );
                            v___x_2284_ = lean_string_append(v___x_2281_, v___x_2283_);
                            crate::leanh::lean_dec_ref(v___x_2283_);
                            v___x_2285_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                            v___x_2286_ = lean_string_append(v___x_2284_, v___x_2285_);
                            v___x_2287_ = 3;
                            v___x_2288_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_2288_, 0, v___x_2286_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_2288_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_2287_,
                            );
                            v___x_2289_ = lean_array_get_size(v_a_2263_);
                            v___x_2290_ = lean_array_push(v_a_2263_, v___x_2288_);
                            v___x_2291_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2291_, 0, v___x_2289_);
                            crate::leanh::lean_ctor_set(v___x_2291_, 1, v___x_2290_);
                            return v___x_2291_;
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec_ref(v_a_2258_);
                        v_toContext_2292_ = crate::leanh::lean_ctor_get(v_a_2262_, 1);
                        v_package_2293_ = crate::leanh::lean_ctor_get(v_self_2257_, 0);
                        crate::leanh::lean_inc(v_package_2293_);
                        crate::leanh::lean_dec_ref_known(v_self_2257_, 1);
                        v_packageMap_2294_ = crate::leanh::lean_ctor_get(v_toContext_2292_, 5);
                        v___x_2295_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_2294_, v_package_2293_);
                        if crate::leanh::lean_obj_tag(v___x_2295_) == 1 {
                            crate::leanh::lean_dec(v_package_2293_);
                            crate::leanh::lean_dec_ref(v_root_2256_);
                            v_val_2296_ = crate::leanh::lean_ctor_get(v___x_2295_, 0);
                            crate::leanh::lean_inc(v_val_2296_);
                            crate::leanh::lean_dec_ref_known(v___x_2295_, 1);
                            v___x_2297_ = l_Lake_instDataKindPackage;
                            v___x_2298_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                            v___x_2299_ = 0;
                            v___x_2300_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                            v___x_2301_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2301_, 0, v_val_2296_);
                            crate::leanh::lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                            v___x_2302_ = lean_task_pure(v___x_2301_);
                            v___x_2303_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_2303_, 0, v___x_2302_);
                            crate::leanh::lean_ctor_set(v___x_2303_, 1, v___x_2297_);
                            crate::leanh::lean_ctor_set(v___x_2303_, 2, v___x_2298_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_2303_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                                v___x_2299_,
                            );
                            v___x_2304_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2304_, 0, v___x_2303_);
                            crate::leanh::lean_ctor_set(v___x_2304_, 1, v_a_2263_);
                            return v___x_2304_;
                        } else {
                            crate::leanh::lean_dec(v___x_2295_);
                            v___x_2305_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                            v___x_2306_ = l_Lake_BuildKey_toString(v_root_2256_);
                            v___x_2307_ = lean_string_append(v___x_2305_, v___x_2306_);
                            crate::leanh::lean_dec_ref(v___x_2306_);
                            v___x_2308_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                            v___x_2309_ = lean_string_append(v___x_2307_, v___x_2308_);
                            v___x_2310_ = 1;
                            v___x_2311_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_package_2293_,
                                    v___x_2310_,
                                );
                            v___x_2312_ = lean_string_append(v___x_2309_, v___x_2311_);
                            crate::leanh::lean_dec_ref(v___x_2311_);
                            v___x_2313_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                            v___x_2314_ = lean_string_append(v___x_2312_, v___x_2313_);
                            v___x_2315_ = 3;
                            v___x_2316_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_2316_, 0, v___x_2314_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_2316_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                                v___x_2315_,
                            );
                            v___x_2317_ = lean_array_get_size(v_a_2263_);
                            v___x_2318_ = lean_array_push(v_a_2263_, v___x_2316_);
                            v___x_2319_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2319_, 0, v___x_2317_);
                            crate::leanh::lean_ctor_set(v___x_2319_, 1, v___x_2318_);
                            return v___x_2319_;
                        }
                    }
                    2 => {
                        crate::leanh::lean_dec_ref(v_a_2258_);
                        v_toContext_2320_ = crate::leanh::lean_ctor_get(v_a_2262_, 1);
                        v_package_2321_ = crate::leanh::lean_ctor_get(v_self_2257_, 0);
                        v_module_2322_ = crate::leanh::lean_ctor_get(v_self_2257_, 1);
                        v_isSharedCheck_2380_ =
                            (!crate::leanh::lean_is_exclusive(v_self_2257_)) as u8;
                        if v_isSharedCheck_2380_ == 0 {
                            v___x_2324_ = v_self_2257_;
                            v_isShared_2325_ = v_isSharedCheck_2380_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_module_2322_);
                            crate::leanh::lean_inc(v_package_2321_);
                            crate::leanh::lean_dec(v_self_2257_);
                            v___x_2324_ = crate::leanh::lean_box(0);
                            v_isShared_2325_ = v_isSharedCheck_2380_;
                            state = 1;
                            continue;
                        }
                    }
                    3 => {
                        v_toContext_2381_ = crate::leanh::lean_ctor_get(v_a_2262_, 1);
                        v_package_2382_ = crate::leanh::lean_ctor_get(v_self_2257_, 0);
                        v_target_2383_ = crate::leanh::lean_ctor_get(v_self_2257_, 1);
                        v_isSharedCheck_2411_ =
                            (!crate::leanh::lean_is_exclusive(v_self_2257_)) as u8;
                        if v_isSharedCheck_2411_ == 0 {
                            v___x_2385_ = v_self_2257_;
                            v_isShared_2386_ = v_isSharedCheck_2411_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_target_2383_);
                            crate::leanh::lean_inc(v_package_2382_);
                            crate::leanh::lean_dec(v_self_2257_);
                            v___x_2385_ = crate::leanh::lean_box(0);
                            v_isShared_2386_ = v_isSharedCheck_2411_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v_target_2412_ = crate::leanh::lean_ctor_get(v_self_2257_, 0);
                        v_facet_2413_ = crate::leanh::lean_ctor_get(v_self_2257_, 1);
                        crate::leanh::lean_inc_ref(v_a_2258_);
                        crate::leanh::lean_inc_ref(v_target_2412_);
                        crate::leanh::lean_inc_ref(v_root_2256_);
                        v___x_2414_ =
                            l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(
                                v_root_2256_,
                                v_target_2412_,
                                v_a_2258_,
                                v_a_2259_,
                                v_a_2260_,
                                v_a_2261_,
                                v_a_2262_,
                                v_a_2263_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_2414_) == 0 {
                            v_a_2415_ = crate::leanh::lean_ctor_get(v___x_2414_, 0);
                            v_a_2416_ = crate::leanh::lean_ctor_get(v___x_2414_, 1);
                            v_isSharedCheck_2463_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2414_)) as u8;
                            if v_isSharedCheck_2463_ == 0 {
                                v___x_2418_ = v___x_2414_;
                                v_isShared_2419_ = v_isSharedCheck_2463_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2416_);
                                crate::leanh::lean_inc(v_a_2415_);
                                crate::leanh::lean_dec(v___x_2414_);
                                v___x_2418_ = crate::leanh::lean_box(0);
                                v_isShared_2419_ = v_isSharedCheck_2463_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_self_2257_, 2);
                            crate::leanh::lean_dec_ref(v_a_2258_);
                            crate::leanh::lean_dec_ref(v_root_2256_);
                            return v___x_2414_;
                        }
                    }
                }
            }
            1 => {
                v_packageMap_2326_ = crate::leanh::lean_ctor_get(v_toContext_2320_, 5);
                v___x_2327_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_2326_, v_package_2321_);
                if crate::leanh::lean_obj_tag(v___x_2327_) == 1 {
                    crate::leanh::lean_dec(v_package_2321_);
                    v_val_2328_ = crate::leanh::lean_ctor_get(v___x_2327_, 0);
                    crate::leanh::lean_inc_n(v_val_2328_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2327_, 1);
                    crate::leanh::lean_inc(v_module_2322_);
                    v___x_2329_ = l_Lake_Package_findTargetModule_x3f(v_module_2322_, v_val_2328_);
                    if crate::leanh::lean_obj_tag(v___x_2329_) == 1 {
                        crate::leanh::lean_dec(v_val_2328_);
                        crate::leanh::lean_dec(v_module_2322_);
                        crate::leanh::lean_dec_ref(v_root_2256_);
                        v_val_2330_ = crate::leanh::lean_ctor_get(v___x_2329_, 0);
                        crate::leanh::lean_inc(v_val_2330_);
                        crate::leanh::lean_dec_ref_known(v___x_2329_, 1);
                        v___x_2331_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                        v___x_2332_ = 0;
                        v___x_2333_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                        if v_isShared_2325_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2324_, 0);
                            crate::leanh::lean_ctor_set(v___x_2324_, 1, v___x_2333_);
                            crate::leanh::lean_ctor_set(v___x_2324_, 0, v_val_2330_);
                            v___x_2335_ = v___x_2324_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2339_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_val_2330_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2333_);
                            v___x_2335_ = v_reuseFailAlloc_2339_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2329_);
                        v_baseName_2340_ = crate::leanh::lean_ctor_get(v_val_2328_, 1);
                        crate::leanh::lean_inc(v_baseName_2340_);
                        crate::leanh::lean_dec(v_val_2328_);
                        v___x_2341_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_2342_ = l_Lake_BuildKey_toString(v_root_2256_);
                        v___x_2343_ = lean_string_append(v___x_2341_, v___x_2342_);
                        crate::leanh::lean_dec_ref(v___x_2342_);
                        v___x_2344_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5;
                        v___x_2345_ = lean_string_append(v___x_2343_, v___x_2344_);
                        v___x_2346_ = 1;
                        v___x_2347_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_module_2322_,
                                v___x_2346_,
                            );
                        v___x_2348_ = lean_string_append(v___x_2345_, v___x_2347_);
                        crate::leanh::lean_dec_ref(v___x_2347_);
                        v___x_2349_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7;
                        v___x_2350_ = lean_string_append(v___x_2348_, v___x_2349_);
                        v___x_2351_ = 0;
                        v___x_2352_ = l_Lean_Name_toString(v_baseName_2340_, v___x_2351_);
                        v___x_2353_ = lean_string_append(v___x_2350_, v___x_2352_);
                        crate::leanh::lean_dec_ref(v___x_2352_);
                        v___x_2354_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                        v___x_2355_ = lean_string_append(v___x_2353_, v___x_2354_);
                        v___x_2356_ = 3;
                        v___x_2357_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2357_, 0, v___x_2355_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2357_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2356_,
                        );
                        v___x_2358_ = lean_array_get_size(v_a_2263_);
                        v___x_2359_ = lean_array_push(v_a_2263_, v___x_2357_);
                        if v_isShared_2325_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2324_, 1);
                            crate::leanh::lean_ctor_set(v___x_2324_, 1, v___x_2359_);
                            crate::leanh::lean_ctor_set(v___x_2324_, 0, v___x_2358_);
                            v___x_2361_ = v___x_2324_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2362_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2358_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___x_2359_);
                            v___x_2361_ = v_reuseFailAlloc_2362_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2327_);
                    crate::leanh::lean_dec(v_module_2322_);
                    v___x_2363_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_2364_ = l_Lake_BuildKey_toString(v_root_2256_);
                    v___x_2365_ = lean_string_append(v___x_2363_, v___x_2364_);
                    crate::leanh::lean_dec_ref(v___x_2364_);
                    v___x_2366_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                    v___x_2367_ = lean_string_append(v___x_2365_, v___x_2366_);
                    v___x_2368_ = 1;
                    v___x_2369_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_package_2321_,
                        v___x_2368_,
                    );
                    v___x_2370_ = lean_string_append(v___x_2367_, v___x_2369_);
                    crate::leanh::lean_dec_ref(v___x_2369_);
                    v___x_2371_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                    v___x_2372_ = lean_string_append(v___x_2370_, v___x_2371_);
                    v___x_2373_ = 3;
                    v___x_2374_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2374_, 0, v___x_2372_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2374_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2373_,
                    );
                    v___x_2375_ = lean_array_get_size(v_a_2263_);
                    v___x_2376_ = lean_array_push(v_a_2263_, v___x_2374_);
                    if v_isShared_2325_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2324_, 1);
                        crate::leanh::lean_ctor_set(v___x_2324_, 1, v___x_2376_);
                        crate::leanh::lean_ctor_set(v___x_2324_, 0, v___x_2375_);
                        v___x_2378_ = v___x_2324_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2379_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2375_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2376_);
                        v___x_2378_ = v_reuseFailAlloc_2379_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2336_ = lean_task_pure(v___x_2335_);
                v___x_2337_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2337_, 0, v___x_2336_);
                crate::leanh::lean_ctor_set(v___x_2337_, 1, v___x_2265_);
                crate::leanh::lean_ctor_set(v___x_2337_, 2, v___x_2331_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2337_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2332_,
                );
                v___x_2338_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2338_, 0, v___x_2337_);
                crate::leanh::lean_ctor_set(v___x_2338_, 1, v_a_2263_);
                return v___x_2338_;
            }
            3 => {
                return v___x_2361_;
            }
            4 => {
                return v___x_2378_;
            }
            5 => {
                v_packageMap_2387_ = crate::leanh::lean_ctor_get(v_toContext_2381_, 5);
                v___x_2388_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_2387_, v_package_2382_);
                if crate::leanh::lean_obj_tag(v___x_2388_) == 1 {
                    crate::leanh::lean_dec(v_package_2382_);
                    crate::leanh::lean_dec_ref(v_root_2256_);
                    v_val_2389_ = crate::leanh::lean_ctor_get(v___x_2388_, 0);
                    crate::leanh::lean_inc(v_val_2389_);
                    crate::leanh::lean_dec_ref_known(v___x_2388_, 1);
                    if v_isShared_2386_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2385_, 0);
                        crate::leanh::lean_ctor_set(v___x_2385_, 0, v_val_2389_);
                        v___x_2391_ = v___x_2385_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2393_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_val_2389_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_target_2383_);
                        v___x_2391_ = v_reuseFailAlloc_2393_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2388_);
                    crate::leanh::lean_dec(v_target_2383_);
                    crate::leanh::lean_dec_ref(v_a_2258_);
                    v___x_2394_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_2395_ = l_Lake_BuildKey_toString(v_root_2256_);
                    v___x_2396_ = lean_string_append(v___x_2394_, v___x_2395_);
                    crate::leanh::lean_dec_ref(v___x_2395_);
                    v___x_2397_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                    v___x_2398_ = lean_string_append(v___x_2396_, v___x_2397_);
                    v___x_2399_ = 1;
                    v___x_2400_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_package_2382_,
                        v___x_2399_,
                    );
                    v___x_2401_ = lean_string_append(v___x_2398_, v___x_2400_);
                    crate::leanh::lean_dec_ref(v___x_2400_);
                    v___x_2402_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                    v___x_2403_ = lean_string_append(v___x_2401_, v___x_2402_);
                    v___x_2404_ = 3;
                    v___x_2405_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2405_, 0, v___x_2403_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2405_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2404_,
                    );
                    v___x_2406_ = lean_array_get_size(v_a_2263_);
                    v___x_2407_ = lean_array_push(v_a_2263_, v___x_2405_);
                    if v_isShared_2386_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2385_, 1);
                        crate::leanh::lean_ctor_set(v___x_2385_, 1, v___x_2407_);
                        crate::leanh::lean_ctor_set(v___x_2385_, 0, v___x_2406_);
                        v___x_2409_ = v___x_2385_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2410_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2406_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2410_, 1, v___x_2407_);
                        v___x_2409_ = v_reuseFailAlloc_2410_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v_a_2262_);
                crate::leanh::lean_inc(v_a_2261_);
                crate::leanh::lean_inc(v_a_2260_);
                crate::leanh::lean_inc(v_a_2259_);
                v___x_2392_ = crate::leanh::lean_apply_7(
                    v_a_2258_,
                    v___x_2391_,
                    v_a_2259_,
                    v_a_2260_,
                    v_a_2261_,
                    v_a_2262_,
                    v_a_2263_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2392_;
            }
            7 => {
                return v___x_2409_;
            }
            8 => {
                v_kind_2420_ = crate::leanh::lean_ctor_get(v_a_2415_, 1);
                v___x_2421_ = l_Lean_Name_isAnonymous(v_kind_2420_);
                if v___x_2421_ == 0 {
                    crate::leanh::lean_inc(v_facet_2413_);
                    crate::leanh::lean_inc_ref(v_target_2412_);
                    crate::leanh::lean_dec_ref_known(v_self_2257_, 2);
                    v_toContext_2422_ = crate::leanh::lean_ctor_get(v_a_2262_, 1);
                    v_facetConfigs_2423_ = crate::leanh::lean_ctor_get(v_toContext_2422_, 6);
                    v___x_2424_ =
                        l_Lake_FacetConfigMap_get_x3f(v_facet_2413_, v_facetConfigs_2423_);
                    if crate::leanh::lean_obj_tag(v___x_2424_) == 1 {
                        crate::leanh::lean_dec_ref(v_root_2256_);
                        v_val_2425_ = crate::leanh::lean_ctor_get(v___x_2424_, 0);
                        crate::leanh::lean_inc(v_val_2425_);
                        crate::leanh::lean_dec_ref_known(v___x_2424_, 1);
                        v_outKind_2426_ = crate::leanh::lean_ctor_get(v_val_2425_, 2);
                        crate::leanh::lean_inc(v_outKind_2426_);
                        crate::leanh::lean_dec(v_val_2425_);
                        crate::leanh::lean_inc(v_kind_2420_);
                        v___f_2427_ = crate::leanh::lean_alloc_closure(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed as *mut core::ffi::c_void, 11, 3);
                        crate::leanh::lean_closure_set(v___f_2427_, 0, v_target_2412_);
                        crate::leanh::lean_closure_set(v___f_2427_, 1, v_kind_2420_);
                        crate::leanh::lean_closure_set(v___f_2427_, 2, v_facet_2413_);
                        v___x_2428_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2429_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
                        v___x_2430_ = l_Lake_Job_bindM___redArg(
                            v_outKind_2426_,
                            v_a_2415_,
                            v___f_2427_,
                            v___x_2428_,
                            v___x_2421_,
                            v_a_2258_,
                            v_a_2259_,
                            v_a_2260_,
                            v_a_2261_,
                            v_a_2262_,
                            v___x_2429_,
                        );
                        if v_isShared_2419_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2418_, 0, v___x_2430_);
                            v___x_2432_ = v___x_2418_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_2433_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_a_2416_);
                            v___x_2432_ = v_reuseFailAlloc_2433_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2424_);
                        crate::leanh::lean_dec(v_a_2415_);
                        crate::leanh::lean_dec_ref(v_target_2412_);
                        crate::leanh::lean_dec_ref(v_a_2258_);
                        v___x_2434_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_2435_ = l_Lake_BuildKey_toString(v_root_2256_);
                        v___x_2436_ = lean_string_append(v___x_2434_, v___x_2435_);
                        crate::leanh::lean_dec_ref(v___x_2435_);
                        v___x_2437_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11;
                        v___x_2438_ = lean_string_append(v___x_2436_, v___x_2437_);
                        v___x_2439_ = 1;
                        v___x_2440_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_facet_2413_,
                                v___x_2439_,
                            );
                        v___x_2441_ = lean_string_append(v___x_2438_, v___x_2440_);
                        crate::leanh::lean_dec_ref(v___x_2440_);
                        v___x_2442_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                        v___x_2443_ = lean_string_append(v___x_2441_, v___x_2442_);
                        v___x_2444_ = 3;
                        v___x_2445_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_2445_, 0, v___x_2443_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_2445_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_2444_,
                        );
                        v___x_2446_ = lean_array_get_size(v_a_2416_);
                        v___x_2447_ = lean_array_push(v_a_2416_, v___x_2445_);
                        if v_isShared_2419_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_2418_, 1);
                            crate::leanh::lean_ctor_set(v___x_2418_, 1, v___x_2447_);
                            crate::leanh::lean_ctor_set(v___x_2418_, 0, v___x_2446_);
                            v___x_2449_ = v___x_2418_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_2450_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2446_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2450_, 1, v___x_2447_);
                            v___x_2449_ = v_reuseFailAlloc_2450_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2415_);
                    crate::leanh::lean_dec_ref(v_a_2258_);
                    crate::leanh::lean_dec_ref(v_root_2256_);
                    v___x_2451_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_2452_ = l_Lake_BuildKey_toString(v_self_2257_);
                    v___x_2453_ = lean_string_append(v___x_2451_, v___x_2452_);
                    crate::leanh::lean_dec_ref(v___x_2452_);
                    v___x_2454_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13;
                    v___x_2455_ = lean_string_append(v___x_2453_, v___x_2454_);
                    v___x_2456_ = 3;
                    v___x_2457_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2457_, 0, v___x_2455_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2457_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_2456_,
                    );
                    v___x_2458_ = lean_array_get_size(v_a_2416_);
                    v___x_2459_ = lean_array_push(v_a_2416_, v___x_2457_);
                    if v_isShared_2419_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2418_, 1);
                        crate::leanh::lean_ctor_set(v___x_2418_, 1, v___x_2459_);
                        crate::leanh::lean_ctor_set(v___x_2418_, 0, v___x_2458_);
                        v___x_2461_ = v___x_2418_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2462_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2458_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2462_, 1, v___x_2459_);
                        v___x_2461_ = v_reuseFailAlloc_2462_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_2432_;
            }
            10 => {
                return v___x_2449_;
            }
            11 => {
                return v___x_2461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___boxed(
    mut v_root_2464_: *mut crate::leanh::LeanObject,
    mut v_self_2465_: *mut crate::leanh::LeanObject,
    mut v_a_2466_: *mut crate::leanh::LeanObject,
    mut v_a_2467_: *mut crate::leanh::LeanObject,
    mut v_a_2468_: *mut crate::leanh::LeanObject,
    mut v_a_2469_: *mut crate::leanh::LeanObject,
    mut v_a_2470_: *mut crate::leanh::LeanObject,
    mut v_a_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2473_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(
        v_root_2464_,
        v_self_2465_,
        v_a_2466_,
        v_a_2467_,
        v_a_2468_,
        v_a_2469_,
        v_a_2470_,
        v_a_2471_,
    );
    crate::leanh::lean_dec_ref(v_a_2470_);
    crate::leanh::lean_dec(v_a_2469_);
    crate::leanh::lean_dec(v_a_2468_);
    crate::leanh::lean_dec(v_a_2467_);
    return v_res_2473_;
}
pub unsafe fn l_Lake_BuildKey_fetch___redArg(
    mut v_self_2474_: *mut crate::leanh::LeanObject,
    mut v_a_2475_: *mut crate::leanh::LeanObject,
    mut v_a_2476_: *mut crate::leanh::LeanObject,
    mut v_a_2477_: *mut crate::leanh::LeanObject,
    mut v_a_2478_: *mut crate::leanh::LeanObject,
    mut v_a_2479_: *mut crate::leanh::LeanObject,
    mut v_a_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_self_2474_);
    v___x_2482_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(
        v_self_2474_,
        v_self_2474_,
        v_a_2475_,
        v_a_2476_,
        v_a_2477_,
        v_a_2478_,
        v_a_2479_,
        v_a_2480_,
    );
    return v___x_2482_;
}
pub unsafe fn l_Lake_BuildKey_fetch___redArg___boxed(
    mut v_self_2483_: *mut crate::leanh::LeanObject,
    mut v_a_2484_: *mut crate::leanh::LeanObject,
    mut v_a_2485_: *mut crate::leanh::LeanObject,
    mut v_a_2486_: *mut crate::leanh::LeanObject,
    mut v_a_2487_: *mut crate::leanh::LeanObject,
    mut v_a_2488_: *mut crate::leanh::LeanObject,
    mut v_a_2489_: *mut crate::leanh::LeanObject,
    mut v_a_2490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2491_ = l_Lake_BuildKey_fetch___redArg(
        v_self_2483_,
        v_a_2484_,
        v_a_2485_,
        v_a_2486_,
        v_a_2487_,
        v_a_2488_,
        v_a_2489_,
    );
    crate::leanh::lean_dec_ref(v_a_2488_);
    crate::leanh::lean_dec(v_a_2487_);
    crate::leanh::lean_dec(v_a_2486_);
    crate::leanh::lean_dec(v_a_2485_);
    return v_res_2491_;
}
pub unsafe fn l_Lake_BuildKey_fetch(
    mut v_00_u03b1_2492_: *mut crate::leanh::LeanObject,
    mut v_self_2493_: *mut crate::leanh::LeanObject,
    mut v_inst_2494_: *mut crate::leanh::LeanObject,
    mut v_a_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
    mut v_a_2497_: *mut crate::leanh::LeanObject,
    mut v_a_2498_: *mut crate::leanh::LeanObject,
    mut v_a_2499_: *mut crate::leanh::LeanObject,
    mut v_a_2500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_self_2493_);
    v___x_2502_ = l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(
        v_self_2493_,
        v_self_2493_,
        v_a_2495_,
        v_a_2496_,
        v_a_2497_,
        v_a_2498_,
        v_a_2499_,
        v_a_2500_,
    );
    return v___x_2502_;
}
pub unsafe fn l_Lake_BuildKey_fetch___boxed(
    mut v_00_u03b1_2503_: *mut crate::leanh::LeanObject,
    mut v_self_2504_: *mut crate::leanh::LeanObject,
    mut v_inst_2505_: *mut crate::leanh::LeanObject,
    mut v_a_2506_: *mut crate::leanh::LeanObject,
    mut v_a_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
    mut v_a_2509_: *mut crate::leanh::LeanObject,
    mut v_a_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2513_ = l_Lake_BuildKey_fetch(
        v_00_u03b1_2503_,
        v_self_2504_,
        v_inst_2505_,
        v_a_2506_,
        v_a_2507_,
        v_a_2508_,
        v_a_2509_,
        v_a_2510_,
        v_a_2511_,
    );
    crate::leanh::lean_dec_ref(v_a_2510_);
    crate::leanh::lean_dec(v_a_2509_);
    crate::leanh::lean_dec(v_a_2508_);
    crate::leanh::lean_dec(v_a_2507_);
    return v_res_2513_;
}
pub unsafe fn l_Lake_Target_fetchIn___redArg(
    mut v_inst_2518_: *mut crate::leanh::LeanObject,
    mut v_defaultPkg_2519_: *mut crate::leanh::LeanObject,
    mut v_self_2520_: *mut crate::leanh::LeanObject,
    mut v_a_2521_: *mut crate::leanh::LeanObject,
    mut v_a_2522_: *mut crate::leanh::LeanObject,
    mut v_a_2523_: *mut crate::leanh::LeanObject,
    mut v_a_2524_: *mut crate::leanh::LeanObject,
    mut v_a_2525_: *mut crate::leanh::LeanObject,
    mut v_a_2526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2534_: u8 = 0;
    let mut v___y_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2557_: u8 = 0;
    let mut v_kind_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v___x_2560_: u8 = 0;
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2569_: u8 = 0;
    let mut v_unused_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2571_: u8 = 0;
    let mut v_a_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2576_: u8 = 0;
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2528_ = 1;
                crate::leanh::lean_inc_ref_n(v_self_2520_, 2);
                v___x_2529_ =
                    l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
                        v_defaultPkg_2519_,
                        v_self_2520_,
                        v_self_2520_,
                        v___x_2528_,
                        v_a_2521_,
                        v_a_2522_,
                        v_a_2523_,
                        v_a_2524_,
                        v_a_2525_,
                        v_a_2526_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2529_) == 0 {
                    v_a_2530_ = crate::leanh::lean_ctor_get(v___x_2529_, 0);
                    v_a_2531_ = crate::leanh::lean_ctor_get(v___x_2529_, 1);
                    v_isSharedCheck_2571_ = (!crate::leanh::lean_is_exclusive(v___x_2529_)) as u8;
                    if v_isSharedCheck_2571_ == 0 {
                        v___x_2533_ = v___x_2529_;
                        v_isShared_2534_ = v_isSharedCheck_2571_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2531_);
                        crate::leanh::lean_inc(v_a_2530_);
                        crate::leanh::lean_dec(v___x_2529_);
                        v___x_2533_ = crate::leanh::lean_box(0);
                        v_isShared_2534_ = v_isSharedCheck_2571_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_self_2520_);
                    crate::leanh::lean_dec(v_inst_2518_);
                    v_a_2572_ = crate::leanh::lean_ctor_get(v___x_2529_, 0);
                    v_a_2573_ = crate::leanh::lean_ctor_get(v___x_2529_, 1);
                    v_isSharedCheck_2580_ = (!crate::leanh::lean_is_exclusive(v___x_2529_)) as u8;
                    if v_isSharedCheck_2580_ == 0 {
                        v___x_2575_ = v___x_2529_;
                        v_isShared_2576_ = v_isSharedCheck_2580_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2573_);
                        crate::leanh::lean_inc(v_a_2572_);
                        crate::leanh::lean_dec(v___x_2529_);
                        v___x_2575_ = crate::leanh::lean_box(0);
                        v_isShared_2576_ = v_isSharedCheck_2580_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2554_ = crate::leanh::lean_ctor_get(v_a_2530_, 1);
                v_isSharedCheck_2569_ = (!crate::leanh::lean_is_exclusive(v_a_2530_)) as u8;
                if v_isSharedCheck_2569_ == 0 {
                    v_unused_2570_ = crate::leanh::lean_ctor_get(v_a_2530_, 0);
                    crate::leanh::lean_dec(v_unused_2570_);
                    v___x_2556_ = v_a_2530_;
                    v_isShared_2557_ = v_isSharedCheck_2569_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2554_);
                    crate::leanh::lean_dec(v_a_2530_);
                    v___x_2556_ = crate::leanh::lean_box(0);
                    v_isShared_2557_ = v_isSharedCheck_2569_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2537_ = l_Lake_Target_fetchIn___redArg___closed__0;
                v___x_2538_ = l_Lake_PartialBuildKey_toString(v_self_2520_);
                v___x_2539_ = lean_string_append(v___x_2537_, v___x_2538_);
                crate::leanh::lean_dec_ref(v___x_2538_);
                v___x_2540_ = l_Lake_Target_fetchIn___redArg___closed__1;
                v___x_2541_ = lean_string_append(v___x_2539_, v___x_2540_);
                v___x_2542_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_inst_2518_,
                    v___x_2528_,
                );
                v___x_2543_ = lean_string_append(v___x_2541_, v___x_2542_);
                crate::leanh::lean_dec_ref(v___x_2542_);
                v___x_2544_ = l_Lake_Target_fetchIn___redArg___closed__2;
                v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
                v___x_2546_ = lean_string_append(v___x_2545_, v___y_2536_);
                crate::leanh::lean_dec_ref(v___y_2536_);
                v___x_2547_ = 3;
                v___x_2548_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2548_, 0, v___x_2546_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2548_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2547_,
                );
                v___x_2549_ = lean_array_get_size(v_a_2531_);
                v___x_2550_ = lean_array_push(v_a_2531_, v___x_2548_);
                if v_isShared_2534_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2533_, 1);
                    crate::leanh::lean_ctor_set(v___x_2533_, 1, v___x_2550_);
                    crate::leanh::lean_ctor_set(v___x_2533_, 0, v___x_2549_);
                    v___x_2552_ = v___x_2533_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2553_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2549_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2550_);
                    v___x_2552_ = v_reuseFailAlloc_2553_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2552_;
            }
            4 => {
                v_kind_2558_ = crate::leanh::lean_ctor_get(v_snd_2554_, 1);
                v___x_2559_ = lean_name_eq(v_kind_2558_, v_inst_2518_);
                if v___x_2559_ == 0 {
                    crate::leanh::lean_inc(v_kind_2558_);
                    crate::leanh::lean_del_object(v___x_2556_);
                    crate::leanh::lean_dec(v_snd_2554_);
                    v___x_2560_ = l_Lean_Name_isAnonymous(v_kind_2558_);
                    if v___x_2560_ == 0 {
                        v___x_2561_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                        v___x_2562_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_2558_,
                                v___x_2528_,
                            );
                        v___x_2563_ = lean_string_append(v___x_2561_, v___x_2562_);
                        crate::leanh::lean_dec_ref(v___x_2562_);
                        v___x_2564_ = lean_string_append(v___x_2563_, v___x_2561_);
                        v___y_2536_ = v___x_2564_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_kind_2558_);
                        v___x_2565_ = l_Lake_Target_fetchIn___redArg___closed__3;
                        v___y_2536_ = v___x_2565_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2533_);
                    crate::leanh::lean_dec_ref(v_self_2520_);
                    crate::leanh::lean_dec(v_inst_2518_);
                    if v_isShared_2557_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2556_, 1, v_a_2531_);
                        crate::leanh::lean_ctor_set(v___x_2556_, 0, v_snd_2554_);
                        v___x_2567_ = v___x_2556_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2568_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_snd_2554_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_a_2531_);
                        v___x_2567_ = v_reuseFailAlloc_2568_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2567_;
            }
            6 => {
                if v_isShared_2576_ == 0 {
                    v___x_2578_ = v___x_2575_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2579_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_a_2573_);
                    v___x_2578_ = v_reuseFailAlloc_2579_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_Target_fetchIn___redArg___boxed(
    mut v_inst_2581_: *mut crate::leanh::LeanObject,
    mut v_defaultPkg_2582_: *mut crate::leanh::LeanObject,
    mut v_self_2583_: *mut crate::leanh::LeanObject,
    mut v_a_2584_: *mut crate::leanh::LeanObject,
    mut v_a_2585_: *mut crate::leanh::LeanObject,
    mut v_a_2586_: *mut crate::leanh::LeanObject,
    mut v_a_2587_: *mut crate::leanh::LeanObject,
    mut v_a_2588_: *mut crate::leanh::LeanObject,
    mut v_a_2589_: *mut crate::leanh::LeanObject,
    mut v_a_2590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2591_ = l_Lake_Target_fetchIn___redArg(
        v_inst_2581_,
        v_defaultPkg_2582_,
        v_self_2583_,
        v_a_2584_,
        v_a_2585_,
        v_a_2586_,
        v_a_2587_,
        v_a_2588_,
        v_a_2589_,
    );
    crate::leanh::lean_dec_ref(v_a_2588_);
    crate::leanh::lean_dec(v_a_2587_);
    crate::leanh::lean_dec(v_a_2586_);
    crate::leanh::lean_dec(v_a_2585_);
    return v_res_2591_;
}
pub unsafe fn l_Lake_Target_fetchIn(
    mut v_00_u03b1_2592_: *mut crate::leanh::LeanObject,
    mut v_inst_2593_: *mut crate::leanh::LeanObject,
    mut v_defaultPkg_2594_: *mut crate::leanh::LeanObject,
    mut v_self_2595_: *mut crate::leanh::LeanObject,
    mut v_a_2596_: *mut crate::leanh::LeanObject,
    mut v_a_2597_: *mut crate::leanh::LeanObject,
    mut v_a_2598_: *mut crate::leanh::LeanObject,
    mut v_a_2599_: *mut crate::leanh::LeanObject,
    mut v_a_2600_: *mut crate::leanh::LeanObject,
    mut v_a_2601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2603_ = l_Lake_Target_fetchIn___redArg(
        v_inst_2593_,
        v_defaultPkg_2594_,
        v_self_2595_,
        v_a_2596_,
        v_a_2597_,
        v_a_2598_,
        v_a_2599_,
        v_a_2600_,
        v_a_2601_,
    );
    return v___x_2603_;
}
pub unsafe fn l_Lake_Target_fetchIn___boxed(
    mut v_00_u03b1_2604_: *mut crate::leanh::LeanObject,
    mut v_inst_2605_: *mut crate::leanh::LeanObject,
    mut v_defaultPkg_2606_: *mut crate::leanh::LeanObject,
    mut v_self_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
    mut v_a_2610_: *mut crate::leanh::LeanObject,
    mut v_a_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: *mut crate::leanh::LeanObject,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2615_ = l_Lake_Target_fetchIn(
        v_00_u03b1_2604_,
        v_inst_2605_,
        v_defaultPkg_2606_,
        v_self_2607_,
        v_a_2608_,
        v_a_2609_,
        v_a_2610_,
        v_a_2611_,
        v_a_2612_,
        v_a_2613_,
    );
    crate::leanh::lean_dec_ref(v_a_2612_);
    crate::leanh::lean_dec(v_a_2611_);
    crate::leanh::lean_dec(v_a_2610_);
    crate::leanh::lean_dec(v_a_2609_);
    return v_res_2615_;
}
pub unsafe fn l_Lake_TargetArray_fetchIn___redArg___lam__0(
    mut v_inst_2616_: *mut crate::leanh::LeanObject,
    mut v_defaultPkg_2617_: *mut crate::leanh::LeanObject,
    mut v_x_2618_: *mut crate::leanh::LeanObject,
    mut v___y_2619_: *mut crate::leanh::LeanObject,
    mut v___y_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
    mut v___y_2622_: *mut crate::leanh::LeanObject,
    mut v___y_2623_: *mut crate::leanh::LeanObject,
    mut v___y_2624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2626_ = l_Lake_Target_fetchIn___redArg(
        v_inst_2616_,
        v_defaultPkg_2617_,
        v_x_2618_,
        v___y_2619_,
        v___y_2620_,
        v___y_2621_,
        v___y_2622_,
        v___y_2623_,
        v___y_2624_,
    );
    return v___x_2626_;
}
pub unsafe fn l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed(
    mut v_inst_2627_: *mut crate::leanh::LeanObject,
    mut v_defaultPkg_2628_: *mut crate::leanh::LeanObject,
    mut v_x_2629_: *mut crate::leanh::LeanObject,
    mut v___y_2630_: *mut crate::leanh::LeanObject,
    mut v___y_2631_: *mut crate::leanh::LeanObject,
    mut v___y_2632_: *mut crate::leanh::LeanObject,
    mut v___y_2633_: *mut crate::leanh::LeanObject,
    mut v___y_2634_: *mut crate::leanh::LeanObject,
    mut v___y_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2637_ = l_Lake_TargetArray_fetchIn___redArg___lam__0(
        v_inst_2627_,
        v_defaultPkg_2628_,
        v_x_2629_,
        v___y_2630_,
        v___y_2631_,
        v___y_2632_,
        v___y_2633_,
        v___y_2634_,
        v___y_2635_,
    );
    crate::leanh::lean_dec_ref(v___y_2634_);
    crate::leanh::lean_dec(v___y_2633_);
    crate::leanh::lean_dec(v___y_2632_);
    crate::leanh::lean_dec(v___y_2631_);
    return v_res_2637_;
}
pub unsafe fn l_Lake_TargetArray_fetchIn___redArg(
    mut v_inst_2638_: *mut crate::leanh::LeanObject,
    mut v_defaultPkg_2639_: *mut crate::leanh::LeanObject,
    mut v_self_2640_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
    mut v_a_2643_: *mut crate::leanh::LeanObject,
    mut v_a_2644_: *mut crate::leanh::LeanObject,
    mut v_a_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
    mut v_a_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2668_: usize = 0;
    let mut v___x_2669_: usize = 0;
    let mut v___x_521__overap_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2676_: u8 = 0;
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2681_: u8 = 0;
    let mut v_a_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2686_: u8 = 0;
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2690_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2649_ = l_instMonadBaseIO;
                v_toApplicative_2650_ = crate::leanh::lean_ctor_get(v___x_2649_, 0);
                v_toBind_2651_ = crate::leanh::lean_ctor_get(v___x_2649_, 1);
                v_toFunctor_2652_ = crate::leanh::lean_ctor_get(v_toApplicative_2650_, 0);
                v_toPure_2653_ = crate::leanh::lean_ctor_get(v_toApplicative_2650_, 1);
                v___f_2654_ = crate::leanh::lean_alloc_closure(
                    l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    10,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2654_, 0, v_inst_2638_);
                crate::leanh::lean_closure_set(v___f_2654_, 1, v_defaultPkg_2639_);
                crate::leanh::lean_inc_n(v_toBind_2651_, 3);
                crate::leanh::lean_inc_n(v_toPure_2653_, 5);
                v___f_2655_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2655_, 0, v_toPure_2653_);
                crate::leanh::lean_closure_set(v___f_2655_, 1, v_toBind_2651_);
                v___f_2656_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2656_, 0, v_toPure_2653_);
                crate::leanh::lean_closure_set(v___f_2656_, 1, v_toBind_2651_);
                crate::leanh::lean_inc_ref(v___f_2655_);
                v___f_2657_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2657_, 0, v_toPure_2653_);
                crate::leanh::lean_closure_set(v___f_2657_, 1, v___f_2655_);
                crate::leanh::lean_inc_ref_n(v_toFunctor_2652_, 2);
                v___f_2658_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2658_, 0, v_toFunctor_2652_);
                crate::leanh::lean_closure_set(v___f_2658_, 1, v_toPure_2653_);
                crate::leanh::lean_closure_set(v___f_2658_, 2, v_toBind_2651_);
                v___x_2659_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_2652_);
                v___f_2660_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2660_, 0, v_toPure_2653_);
                v___x_2661_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2661_, 0, v___x_2659_);
                crate::leanh::lean_ctor_set(v___x_2661_, 1, v___f_2660_);
                crate::leanh::lean_ctor_set(v___x_2661_, 2, v___f_2658_);
                crate::leanh::lean_ctor_set(v___x_2661_, 3, v___f_2657_);
                crate::leanh::lean_ctor_set(v___x_2661_, 4, v___f_2656_);
                v___x_2662_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2662_, 0, v___x_2661_);
                crate::leanh::lean_ctor_set(v___x_2662_, 1, v___f_2655_);
                v___x_2663_ = l_ReaderT_instMonad___redArg(v___x_2662_);
                v___x_2664_ = l_StateRefT_x27_instMonad___redArg(v___x_2663_);
                v___x_2665_ = l_ReaderT_instMonad___redArg(v___x_2664_);
                v___x_2666_ = l_ReaderT_instMonad___redArg(v___x_2665_);
                v___x_2667_ = l_Lake_EquipT_instMonad___redArg(v___x_2666_);
                v_sz_2668_ = lean_array_size(v_self_2640_);
                v___x_2669_ = 0usize;
                v___x_521__overap_2670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_2667_,
                    v___f_2654_,
                    v_sz_2668_,
                    v___x_2669_,
                    v_self_2640_,
                );
                crate::leanh::lean_inc_ref(v_a_2646_);
                crate::leanh::lean_inc(v_a_2645_);
                crate::leanh::lean_inc(v_a_2644_);
                crate::leanh::lean_inc(v_a_2643_);
                v___x_2671_ = crate::leanh::lean_apply_7(
                    v___x_521__overap_2670_,
                    v_a_2642_,
                    v_a_2643_,
                    v_a_2644_,
                    v_a_2645_,
                    v_a_2646_,
                    v_a_2647_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_2671_) == 0 {
                    v_a_2672_ = crate::leanh::lean_ctor_get(v___x_2671_, 0);
                    v_a_2673_ = crate::leanh::lean_ctor_get(v___x_2671_, 1);
                    v_isSharedCheck_2681_ = (!crate::leanh::lean_is_exclusive(v___x_2671_)) as u8;
                    if v_isSharedCheck_2681_ == 0 {
                        v___x_2675_ = v___x_2671_;
                        v_isShared_2676_ = v_isSharedCheck_2681_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2673_);
                        crate::leanh::lean_inc(v_a_2672_);
                        crate::leanh::lean_dec(v___x_2671_);
                        v___x_2675_ = crate::leanh::lean_box(0);
                        v_isShared_2676_ = v_isSharedCheck_2681_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_traceCaption_2641_);
                    v_a_2682_ = crate::leanh::lean_ctor_get(v___x_2671_, 0);
                    v_a_2683_ = crate::leanh::lean_ctor_get(v___x_2671_, 1);
                    v_isSharedCheck_2690_ = (!crate::leanh::lean_is_exclusive(v___x_2671_)) as u8;
                    if v_isSharedCheck_2690_ == 0 {
                        v___x_2685_ = v___x_2671_;
                        v_isShared_2686_ = v_isSharedCheck_2690_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2683_);
                        crate::leanh::lean_inc(v_a_2682_);
                        crate::leanh::lean_dec(v___x_2671_);
                        v___x_2685_ = crate::leanh::lean_box(0);
                        v_isShared_2686_ = v_isSharedCheck_2690_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2677_ = l_Lake_Job_collectArray___redArg(v_a_2672_, v_traceCaption_2641_);
                crate::leanh::lean_dec(v_a_2672_);
                if v_isShared_2676_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2675_, 0, v___x_2677_);
                    v___x_2679_ = v___x_2675_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2680_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_a_2673_);
                    v___x_2679_ = v_reuseFailAlloc_2680_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2679_;
            }
            3 => {
                if v_isShared_2686_ == 0 {
                    v___x_2688_ = v___x_2685_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2689_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_a_2683_);
                    v___x_2688_ = v_reuseFailAlloc_2689_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2688_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_TargetArray_fetchIn___redArg___boxed(
    mut v_inst_2691_: *mut crate::leanh::LeanObject,
    mut v_defaultPkg_2692_: *mut crate::leanh::LeanObject,
    mut v_self_2693_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_2694_: *mut crate::leanh::LeanObject,
    mut v_a_2695_: *mut crate::leanh::LeanObject,
    mut v_a_2696_: *mut crate::leanh::LeanObject,
    mut v_a_2697_: *mut crate::leanh::LeanObject,
    mut v_a_2698_: *mut crate::leanh::LeanObject,
    mut v_a_2699_: *mut crate::leanh::LeanObject,
    mut v_a_2700_: *mut crate::leanh::LeanObject,
    mut v_a_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2702_ = l_Lake_TargetArray_fetchIn___redArg(
        v_inst_2691_,
        v_defaultPkg_2692_,
        v_self_2693_,
        v_traceCaption_2694_,
        v_a_2695_,
        v_a_2696_,
        v_a_2697_,
        v_a_2698_,
        v_a_2699_,
        v_a_2700_,
    );
    crate::leanh::lean_dec_ref(v_a_2699_);
    crate::leanh::lean_dec(v_a_2698_);
    crate::leanh::lean_dec(v_a_2697_);
    crate::leanh::lean_dec(v_a_2696_);
    return v_res_2702_;
}
pub unsafe fn l_Lake_TargetArray_fetchIn(
    mut v_00_u03b1_2703_: *mut crate::leanh::LeanObject,
    mut v_inst_2704_: *mut crate::leanh::LeanObject,
    mut v_defaultPkg_2705_: *mut crate::leanh::LeanObject,
    mut v_self_2706_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_2707_: *mut crate::leanh::LeanObject,
    mut v_a_2708_: *mut crate::leanh::LeanObject,
    mut v_a_2709_: *mut crate::leanh::LeanObject,
    mut v_a_2710_: *mut crate::leanh::LeanObject,
    mut v_a_2711_: *mut crate::leanh::LeanObject,
    mut v_a_2712_: *mut crate::leanh::LeanObject,
    mut v_a_2713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2715_ = l_Lake_TargetArray_fetchIn___redArg(
        v_inst_2704_,
        v_defaultPkg_2705_,
        v_self_2706_,
        v_traceCaption_2707_,
        v_a_2708_,
        v_a_2709_,
        v_a_2710_,
        v_a_2711_,
        v_a_2712_,
        v_a_2713_,
    );
    return v___x_2715_;
}
pub unsafe fn l_Lake_TargetArray_fetchIn___boxed(
    mut v_00_u03b1_2716_: *mut crate::leanh::LeanObject,
    mut v_inst_2717_: *mut crate::leanh::LeanObject,
    mut v_defaultPkg_2718_: *mut crate::leanh::LeanObject,
    mut v_self_2719_: *mut crate::leanh::LeanObject,
    mut v_traceCaption_2720_: *mut crate::leanh::LeanObject,
    mut v_a_2721_: *mut crate::leanh::LeanObject,
    mut v_a_2722_: *mut crate::leanh::LeanObject,
    mut v_a_2723_: *mut crate::leanh::LeanObject,
    mut v_a_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2728_ = l_Lake_TargetArray_fetchIn(
        v_00_u03b1_2716_,
        v_inst_2717_,
        v_defaultPkg_2718_,
        v_self_2719_,
        v_traceCaption_2720_,
        v_a_2721_,
        v_a_2722_,
        v_a_2723_,
        v_a_2724_,
        v_a_2725_,
        v_a_2726_,
    );
    crate::leanh::lean_dec_ref(v_a_2725_);
    crate::leanh::lean_dec(v_a_2724_);
    crate::leanh::lean_dec(v_a_2723_);
    crate::leanh::lean_dec(v_a_2722_);
    return v_res_2728_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Target_Fetch(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Key(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Target_Fetch(
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
pub unsafe fn initialize_Lake_Build_Target_Fetch(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Infos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Monad(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Build_Key(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Target_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Target_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Target_Fetch(builtin);
}
