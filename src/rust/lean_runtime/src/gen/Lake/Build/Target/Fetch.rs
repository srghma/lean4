// Lean compiler output
// Module: Lake.Build.Target.Fetch
// Imports: Lake.Build.Infos Lake.Build.Job.Monad Lake.Config.Monad Lake.Build.Key
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
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_str___override,
    l_ReaderT_instMonad___redArg,
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
use crate::lean_imports_rs::Init::Core::lean_task_pure;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [39, 58, 32, 112, 97, 99, 107, 97, 103, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [39, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 119, 111, 114, 107, 115, 112, 97, 99, 101, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__4_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__5_value) as *mut LeanObject] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12_value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__9_value) as *mut LeanObject] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__12_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__10_value) as *mut LeanObject] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [60, 110, 105, 108, 62, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2_value) as *mut LeanObject;
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [39, 58, 32, 109, 111, 100, 117, 108, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [39, 58, 32, 109, 111, 100, 117, 108, 101, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [39, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 102, 97, 117, 108, 116, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [39, 58, 32, 116, 97, 114, 103, 101, 116, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 32, 105, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [39, 58, 32, 117, 110, 107, 110, 111, 119, 110, 32, 102, 97, 99, 101, 116, 32, 39, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9_value) as *mut LeanObject,9666231177748665885 as *mut LeanObject] };
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12_value) as *mut LeanObject;
pub static l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [39, 58, 32, 116, 97, 114, 103, 101, 116, 115, 32, 111, 102, 32, 111, 112, 97, 113, 117, 101, 32, 100, 97, 116, 97, 32, 107, 105, 110, 100, 115, 32, 100, 111, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 32, 102, 97, 99, 101, 116, 115, 0]};
static mut l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13_value) as *mut LeanObject;
pub static l_Lake_Target_fetchIn___redArg___closed__0_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Target_fetchIn___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Target_fetchIn___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_Target_fetchIn___redArg___closed__1_value: LeanStringObject<14> =
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
        m_data: [39, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 0],
    };
static mut l_Lake_Target_fetchIn___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Target_fetchIn___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_Target_fetchIn___redArg___closed__2_value: LeanStringObject<8> =
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
        m_data: [39, 44, 32, 103, 111, 116, 32, 0],
    };
static mut l_Lake_Target_fetchIn___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Target_fetchIn___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_Target_fetchIn___redArg___closed__3_value: LeanStringObject<8> =
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
        m_data: [117, 110, 107, 110, 111, 119, 110, 0],
    };
static mut l_Lake_Target_fetchIn___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Target_fetchIn___redArg___closed__3_value) as *mut LeanObject;
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(
    mut v_name_1365_: *mut LeanObject,
    mut v___x_1366_: *mut LeanObject,
    mut v___x_1367_: *mut LeanObject,
    mut v_a_1368_: *mut LeanObject,
    mut v_x_1369_: *mut LeanObject,
    mut v___y_1370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_baseName_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    v_baseName_1371_ = lean_ctor_get(v_a_1368_, 1);
    v___x_1372_ = lean_name_eq(v_baseName_1371_, v_name_1365_);
    if v___x_1372_ == 0 {
        let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_a_1368_);
        v___x_1373_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1373_, 0, v___x_1366_);
        return v___x_1373_;
    } else {
        let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_1366_);
        v___x_1374_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1374_, 0, v_a_1368_);
        v___x_1375_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1375_, 0, v___x_1374_);
        v___x_1376_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1376_, 0, v___x_1375_);
        lean_ctor_set(v___x_1376_, 1, v___x_1367_);
        v___x_1377_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1377_, 0, v___x_1376_);
        return v___x_1377_;
    }
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed(
    mut v_name_1378_: *mut LeanObject,
    mut v___x_1379_: *mut LeanObject,
    mut v___x_1380_: *mut LeanObject,
    mut v_a_1381_: *mut LeanObject,
    mut v_x_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1384_: *mut LeanObject = core::ptr::null_mut();
    v_res_1384_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0(v_name_1378_, v___x_1379_, v___x_1380_, v_a_1381_, v_x_1382_, v___y_1383_);
    lean_dec_ref(v___y_1383_);
    lean_dec(v_name_1378_);
    return v_res_1384_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(
    mut v_defaultPkg_1411_: *mut LeanObject,
    mut v_root_1412_: *mut LeanObject,
    mut v_name_1413_: *mut LeanObject,
    mut v_a_1414_: *mut LeanObject,
    mut v_a_1415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packages_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1462_: usize = 0;
    let mut v___x_1463_: usize = 0;
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v_val_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1474_: u8 = 0;
    let mut v_unused_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_name_1413_) {
                0 => {
                    lean_dec_ref(v_root_1412_);
                    v___x_1434_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1434_, 0, v_defaultPkg_1411_);
                    lean_ctor_set(v___x_1434_, 1, v_a_1415_);
                    return v___x_1434_;
                }
                2 => {
                    lean_dec_ref(v_defaultPkg_1411_);
                    v_toContext_1435_ = lean_ctor_get(v_a_1414_, 1);
                    v_packageMap_1436_ = lean_ctor_get(v_toContext_1435_, 5);
                    v___x_1437_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3;
                    lean_inc_ref(v_name_1413_);
                    lean_inc(v_packageMap_1436_);
                    v___x_1438_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                        v___x_1437_,
                        v_packageMap_1436_,
                        v_name_1413_,
                    );
                    if lean_obj_tag(v___x_1438_) == 1 {
                        lean_dec_ref_known(v_name_1413_, 2);
                        lean_dec_ref(v_root_1412_);
                        v_val_1439_ = lean_ctor_get(v___x_1438_, 0);
                        lean_inc(v_val_1439_);
                        lean_dec_ref_known(v___x_1438_, 1);
                        v___x_1440_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1440_, 0, v_val_1439_);
                        lean_ctor_set(v___x_1440_, 1, v_a_1415_);
                        return v___x_1440_;
                    } else {
                        lean_dec(v___x_1438_);
                        v___x_1441_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_1442_ = l_Lake_PartialBuildKey_toString(v_root_1412_);
                        v___x_1443_ = lean_string_append(v___x_1441_, v___x_1442_);
                        lean_dec_ref(v___x_1442_);
                        v___x_1444_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                        v___x_1445_ = lean_string_append(v___x_1443_, v___x_1444_);
                        v___x_1446_ = 1;
                        v___x_1447_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_1413_,
                                v___x_1446_,
                            );
                        v___x_1448_ = lean_string_append(v___x_1445_, v___x_1447_);
                        lean_dec_ref(v___x_1447_);
                        v___x_1449_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                        v___x_1450_ = lean_string_append(v___x_1448_, v___x_1449_);
                        v___x_1451_ = 3;
                        v___x_1452_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1452_, 0, v___x_1450_);
                        lean_ctor_set_uint8(
                            v___x_1452_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1451_,
                        );
                        v___x_1453_ = lean_array_get_size(v_a_1415_);
                        v___x_1454_ = lean_array_push(v_a_1415_, v___x_1452_);
                        v___x_1455_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1455_, 0, v___x_1453_);
                        lean_ctor_set(v___x_1455_, 1, v___x_1454_);
                        return v___x_1455_;
                    }
                }
                _ => {
                    lean_dec_ref(v_defaultPkg_1411_);
                    v_toContext_1456_ = lean_ctor_get(v_a_1414_, 1);
                    v_packages_1457_ = lean_ctor_get(v_toContext_1456_, 4);
                    v___x_1458_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13;
                    v___x_1459_ = lean_box(0);
                    v___x_1460_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                    lean_inc(v_name_1413_);
                    v___f_1461_ = lean_alloc_closure(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 3);
                    lean_closure_set(v___f_1461_, 0, v_name_1413_);
                    lean_closure_set(v___f_1461_, 1, v___x_1460_);
                    lean_closure_set(v___f_1461_, 2, v___x_1459_);
                    v_sz_1462_ = lean_array_size(v_packages_1457_);
                    v___x_1463_ = 0usize;
                    lean_inc_ref(v_packages_1457_);
                    v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v___x_1458_,
                        v_packages_1457_,
                        v___f_1461_,
                        v_sz_1462_,
                        v___x_1463_,
                        v___x_1460_,
                    );
                    v_fst_1465_ = lean_ctor_get(v___x_1464_, 0);
                    v_isSharedCheck_1474_ = (!lean_is_exclusive(v___x_1464_)) as u8;
                    if v_isSharedCheck_1474_ == 0 {
                        v_unused_1475_ = lean_ctor_get(v___x_1464_, 1);
                        lean_dec(v_unused_1475_);
                        v___x_1467_ = v___x_1464_;
                        v_isShared_1468_ = v_isSharedCheck_1474_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_1465_);
                        lean_dec(v___x_1464_);
                        v___x_1467_ = lean_box(0);
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
                lean_dec_ref(v___x_1420_);
                v___x_1422_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                v___x_1423_ = lean_string_append(v___x_1421_, v___x_1422_);
                v___x_1424_ = 1;
                v___x_1425_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_1413_,
                    v___x_1424_,
                );
                v___x_1426_ = lean_string_append(v___x_1423_, v___x_1425_);
                lean_dec_ref(v___x_1425_);
                v___x_1427_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                v___x_1428_ = lean_string_append(v___x_1426_, v___x_1427_);
                v___x_1429_ = 3;
                v___x_1430_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_1430_, 0, v___x_1428_);
                lean_ctor_set_uint8(
                    v___x_1430_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1429_,
                );
                v___x_1431_ = lean_array_get_size(v_a_1418_);
                v___x_1432_ = lean_array_push(v_a_1418_, v___x_1430_);
                v___x_1433_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1433_, 0, v___x_1431_);
                lean_ctor_set(v___x_1433_, 1, v___x_1432_);
                return v___x_1433_;
            }
            2 => {
                if lean_obj_tag(v_fst_1465_) == 0 {
                    lean_del_object(v___x_1467_);
                    v_a_1418_ = v_a_1415_;
                    state = 1;
                    continue;
                } else {
                    v_val_1469_ = lean_ctor_get(v_fst_1465_, 0);
                    lean_inc(v_val_1469_);
                    lean_dec_ref_known(v_fst_1465_, 1);
                    if lean_obj_tag(v_val_1469_) == 1 {
                        lean_dec(v_name_1413_);
                        lean_dec_ref(v_root_1412_);
                        v_val_1470_ = lean_ctor_get(v_val_1469_, 0);
                        lean_inc(v_val_1470_);
                        lean_dec_ref_known(v_val_1469_, 1);
                        if v_isShared_1468_ == 0 {
                            lean_ctor_set(v___x_1467_, 1, v_a_1415_);
                            lean_ctor_set(v___x_1467_, 0, v_val_1470_);
                            v___x_1472_ = v___x_1467_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_val_1470_);
                            lean_ctor_set(v_reuseFailAlloc_1473_, 1, v_a_1415_);
                            v___x_1472_ = v_reuseFailAlloc_1473_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_1469_);
                        lean_del_object(v___x_1467_);
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
    mut v_defaultPkg_1476_: *mut LeanObject,
    mut v_root_1477_: *mut LeanObject,
    mut v_name_1478_: *mut LeanObject,
    mut v_a_1479_: *mut LeanObject,
    mut v_a_1480_: *mut LeanObject,
    mut v_a_1481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1482_: *mut LeanObject = core::ptr::null_mut();
    v_res_1482_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg(v_defaultPkg_1476_, v_root_1477_, v_name_1478_, v_a_1479_, v_a_1480_);
    lean_dec_ref(v_a_1479_);
    return v_res_1482_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(
    mut v_defaultPkg_1483_: *mut LeanObject,
    mut v_root_1484_: *mut LeanObject,
    mut v_name_1485_: *mut LeanObject,
    mut v_a_1486_: *mut LeanObject,
    mut v_a_1487_: *mut LeanObject,
    mut v_a_1488_: *mut LeanObject,
    mut v_a_1489_: *mut LeanObject,
    mut v_a_1490_: *mut LeanObject,
    mut v_a_1491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: u8 = 0;
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: u8 = 0;
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packages_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1538_: usize = 0;
    let mut v___x_1539_: usize = 0;
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1544_: u8 = 0;
    let mut v_val_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1550_: u8 = 0;
    let mut v_unused_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_name_1485_) {
                0 => {
                    lean_dec_ref(v_root_1484_);
                    v___x_1510_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1510_, 0, v_defaultPkg_1483_);
                    lean_ctor_set(v___x_1510_, 1, v_a_1491_);
                    return v___x_1510_;
                }
                2 => {
                    lean_dec_ref(v_defaultPkg_1483_);
                    v_toContext_1511_ = lean_ctor_get(v_a_1490_, 1);
                    v_packageMap_1512_ = lean_ctor_get(v_toContext_1511_, 5);
                    v___x_1513_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__3;
                    lean_inc_ref(v_name_1485_);
                    lean_inc(v_packageMap_1512_);
                    v___x_1514_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(
                        v___x_1513_,
                        v_packageMap_1512_,
                        v_name_1485_,
                    );
                    if lean_obj_tag(v___x_1514_) == 1 {
                        lean_dec_ref_known(v_name_1485_, 2);
                        lean_dec_ref(v_root_1484_);
                        v_val_1515_ = lean_ctor_get(v___x_1514_, 0);
                        lean_inc(v_val_1515_);
                        lean_dec_ref_known(v___x_1514_, 1);
                        v___x_1516_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1516_, 0, v_val_1515_);
                        lean_ctor_set(v___x_1516_, 1, v_a_1491_);
                        return v___x_1516_;
                    } else {
                        lean_dec(v___x_1514_);
                        v___x_1517_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_1518_ = l_Lake_PartialBuildKey_toString(v_root_1484_);
                        v___x_1519_ = lean_string_append(v___x_1517_, v___x_1518_);
                        lean_dec_ref(v___x_1518_);
                        v___x_1520_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                        v___x_1521_ = lean_string_append(v___x_1519_, v___x_1520_);
                        v___x_1522_ = 1;
                        v___x_1523_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_name_1485_,
                                v___x_1522_,
                            );
                        v___x_1524_ = lean_string_append(v___x_1521_, v___x_1523_);
                        lean_dec_ref(v___x_1523_);
                        v___x_1525_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                        v___x_1526_ = lean_string_append(v___x_1524_, v___x_1525_);
                        v___x_1527_ = 3;
                        v___x_1528_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1528_, 0, v___x_1526_);
                        lean_ctor_set_uint8(
                            v___x_1528_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1527_,
                        );
                        v___x_1529_ = lean_array_get_size(v_a_1491_);
                        v___x_1530_ = lean_array_push(v_a_1491_, v___x_1528_);
                        v___x_1531_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1531_, 0, v___x_1529_);
                        lean_ctor_set(v___x_1531_, 1, v___x_1530_);
                        return v___x_1531_;
                    }
                }
                _ => {
                    lean_dec_ref(v_defaultPkg_1483_);
                    v_toContext_1532_ = lean_ctor_get(v_a_1490_, 1);
                    v_packages_1533_ = lean_ctor_get(v_toContext_1532_, 4);
                    v___x_1534_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__13;
                    v___x_1535_ = lean_box(0);
                    v___x_1536_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                    lean_inc(v_name_1485_);
                    v___f_1537_ = lean_alloc_closure(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 3);
                    lean_closure_set(v___f_1537_, 0, v_name_1485_);
                    lean_closure_set(v___f_1537_, 1, v___x_1536_);
                    lean_closure_set(v___f_1537_, 2, v___x_1535_);
                    v_sz_1538_ = lean_array_size(v_packages_1533_);
                    v___x_1539_ = 0usize;
                    lean_inc_ref(v_packages_1533_);
                    v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v___x_1534_,
                        v_packages_1533_,
                        v___f_1537_,
                        v_sz_1538_,
                        v___x_1539_,
                        v___x_1536_,
                    );
                    v_fst_1541_ = lean_ctor_get(v___x_1540_, 0);
                    v_isSharedCheck_1550_ = (!lean_is_exclusive(v___x_1540_)) as u8;
                    if v_isSharedCheck_1550_ == 0 {
                        v_unused_1551_ = lean_ctor_get(v___x_1540_, 1);
                        lean_dec(v_unused_1551_);
                        v___x_1543_ = v___x_1540_;
                        v_isShared_1544_ = v_isSharedCheck_1550_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fst_1541_);
                        lean_dec(v___x_1540_);
                        v___x_1543_ = lean_box(0);
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
                lean_dec_ref(v___x_1496_);
                v___x_1498_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                v___x_1499_ = lean_string_append(v___x_1497_, v___x_1498_);
                v___x_1500_ = 1;
                v___x_1501_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_1485_,
                    v___x_1500_,
                );
                v___x_1502_ = lean_string_append(v___x_1499_, v___x_1501_);
                lean_dec_ref(v___x_1501_);
                v___x_1503_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                v___x_1504_ = lean_string_append(v___x_1502_, v___x_1503_);
                v___x_1505_ = 3;
                v___x_1506_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_1506_, 0, v___x_1504_);
                lean_ctor_set_uint8(
                    v___x_1506_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1505_,
                );
                v___x_1507_ = lean_array_get_size(v_a_1494_);
                v___x_1508_ = lean_array_push(v_a_1494_, v___x_1506_);
                v___x_1509_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1509_, 0, v___x_1507_);
                lean_ctor_set(v___x_1509_, 1, v___x_1508_);
                return v___x_1509_;
            }
            2 => {
                if lean_obj_tag(v_fst_1541_) == 0 {
                    lean_del_object(v___x_1543_);
                    v_a_1494_ = v_a_1491_;
                    state = 1;
                    continue;
                } else {
                    v_val_1545_ = lean_ctor_get(v_fst_1541_, 0);
                    lean_inc(v_val_1545_);
                    lean_dec_ref_known(v_fst_1541_, 1);
                    if lean_obj_tag(v_val_1545_) == 1 {
                        lean_dec(v_name_1485_);
                        lean_dec_ref(v_root_1484_);
                        v_val_1546_ = lean_ctor_get(v_val_1545_, 0);
                        lean_inc(v_val_1546_);
                        lean_dec_ref_known(v_val_1545_, 1);
                        if v_isShared_1544_ == 0 {
                            lean_ctor_set(v___x_1543_, 1, v_a_1491_);
                            lean_ctor_set(v___x_1543_, 0, v_val_1546_);
                            v___x_1548_ = v___x_1543_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_val_1546_);
                            lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_a_1491_);
                            v___x_1548_ = v_reuseFailAlloc_1549_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_1545_);
                        lean_del_object(v___x_1543_);
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
    mut v_defaultPkg_1552_: *mut LeanObject,
    mut v_root_1553_: *mut LeanObject,
    mut v_name_1554_: *mut LeanObject,
    mut v_a_1555_: *mut LeanObject,
    mut v_a_1556_: *mut LeanObject,
    mut v_a_1557_: *mut LeanObject,
    mut v_a_1558_: *mut LeanObject,
    mut v_a_1559_: *mut LeanObject,
    mut v_a_1560_: *mut LeanObject,
    mut v_a_1561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1562_: *mut LeanObject = core::ptr::null_mut();
    v_res_1562_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD(v_defaultPkg_1552_, v_root_1553_, v_name_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
    lean_dec_ref(v_a_1559_);
    lean_dec(v_a_1558_);
    lean_dec(v_a_1557_);
    lean_dec(v_a_1556_);
    lean_dec_ref(v_a_1555_);
    return v_res_1562_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0(
    mut v_target_1563_: *mut LeanObject,
    mut v_kind_1564_: *mut LeanObject,
    mut v___x_1565_: *mut LeanObject,
    mut v_data_1566_: *mut LeanObject,
    mut v___y_1567_: *mut LeanObject,
    mut v___y_1568_: *mut LeanObject,
    mut v___y_1569_: *mut LeanObject,
    mut v___y_1570_: *mut LeanObject,
    mut v___y_1571_: *mut LeanObject,
    mut v___y_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_log_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_1575_: u8 = 0;
    let mut v_wantsRebuild_1576_: u8 = 0;
    let mut v_trace_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1581_: u8 = 0;
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_a_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1607_: u8 = 0;
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_1574_ = lean_ctor_get(v___y_1572_, 0);
                v_action_1575_ = lean_ctor_get_uint8(
                    v___y_1572_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_1576_ = lean_ctor_get_uint8(
                    v___y_1572_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_1577_ = lean_ctor_get(v___y_1572_, 1);
                v_buildTime_1578_ = lean_ctor_get(v___y_1572_, 2);
                v_isSharedCheck_1608_ = (!lean_is_exclusive(v___y_1572_)) as u8;
                if v_isSharedCheck_1608_ == 0 {
                    v___x_1580_ = v___y_1572_;
                    v_isShared_1581_ = v_isSharedCheck_1608_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buildTime_1578_);
                    lean_inc(v_trace_1577_);
                    lean_inc(v_log_1574_);
                    lean_dec(v___y_1572_);
                    v___x_1580_ = lean_box(0);
                    v_isShared_1581_ = v_isSharedCheck_1608_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1582_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_1582_, 0, v_target_1563_);
                lean_ctor_set(v___x_1582_, 1, v_kind_1564_);
                lean_ctor_set(v___x_1582_, 2, v_data_1566_);
                lean_ctor_set(v___x_1582_, 3, v___x_1565_);
                lean_inc_ref(v___y_1571_);
                lean_inc(v___y_1570_);
                lean_inc(v___y_1569_);
                lean_inc(v___y_1568_);
                v___x_1583_ = lean_apply_7(
                    v___y_1567_,
                    v___x_1582_,
                    v___y_1568_,
                    v___y_1569_,
                    v___y_1570_,
                    v___y_1571_,
                    v_log_1574_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1583_) == 0 {
                    v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
                    v_a_1585_ = lean_ctor_get(v___x_1583_, 1);
                    v_isSharedCheck_1595_ = (!lean_is_exclusive(v___x_1583_)) as u8;
                    if v_isSharedCheck_1595_ == 0 {
                        v___x_1587_ = v___x_1583_;
                        v_isShared_1588_ = v_isSharedCheck_1595_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_1585_);
                        lean_inc(v_a_1584_);
                        lean_dec(v___x_1583_);
                        v___x_1587_ = lean_box(0);
                        v_isShared_1588_ = v_isSharedCheck_1595_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1596_ = lean_ctor_get(v___x_1583_, 0);
                    v_a_1597_ = lean_ctor_get(v___x_1583_, 1);
                    v_isSharedCheck_1607_ = (!lean_is_exclusive(v___x_1583_)) as u8;
                    if v_isSharedCheck_1607_ == 0 {
                        v___x_1599_ = v___x_1583_;
                        v_isShared_1600_ = v_isSharedCheck_1607_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1597_);
                        lean_inc(v_a_1596_);
                        lean_dec(v___x_1583_);
                        v___x_1599_ = lean_box(0);
                        v_isShared_1600_ = v_isSharedCheck_1607_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1581_ == 0 {
                    lean_ctor_set(v___x_1580_, 0, v_a_1585_);
                    v___x_1590_ = v___x_1580_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1585_);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_trace_1577_);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_buildTime_1578_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1594_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_1575_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1594_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1576_,
                    );
                    v___x_1590_ = v_reuseFailAlloc_1594_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1588_ == 0 {
                    lean_ctor_set(v___x_1587_, 1, v___x_1590_);
                    v___x_1592_ = v___x_1587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1584_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1590_);
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
                    lean_ctor_set(v___x_1580_, 0, v_a_1597_);
                    v___x_1602_ = v___x_1580_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1597_);
                    lean_ctor_set(v_reuseFailAlloc_1606_, 1, v_trace_1577_);
                    lean_ctor_set(v_reuseFailAlloc_1606_, 2, v_buildTime_1578_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1606_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_1575_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1606_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_1576_,
                    );
                    v___x_1602_ = v_reuseFailAlloc_1606_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1600_ == 0 {
                    lean_ctor_set(v___x_1599_, 1, v___x_1602_);
                    v___x_1604_ = v___x_1599_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1596_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___x_1602_);
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
    mut v_target_1609_: *mut LeanObject,
    mut v_kind_1610_: *mut LeanObject,
    mut v___x_1611_: *mut LeanObject,
    mut v_data_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
    mut v___y_1617_: *mut LeanObject,
    mut v___y_1618_: *mut LeanObject,
    mut v___y_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1620_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v___y_1617_);
    lean_dec(v___y_1616_);
    lean_dec(v___y_1615_);
    lean_dec(v___y_1614_);
    return v_res_1620_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(
    mut v_t_1621_: *mut LeanObject,
    mut v_k_1622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u8 = 0;
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1621_) == 0 {
                    v_k_1623_ = lean_ctor_get(v_t_1621_, 1);
                    v_v_1624_ = lean_ctor_get(v_t_1621_, 2);
                    v_l_1625_ = lean_ctor_get(v_t_1621_, 3);
                    v_r_1626_ = lean_ctor_get(v_t_1621_, 4);
                    v___x_1627_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1622_, v_k_1623_);
                    match v___x_1627_ {
                        0 => {
                            v_t_1621_ = v_l_1625_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_1624_);
                            v___x_1629_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1629_, 0, v_v_1624_);
                            return v___x_1629_;
                        }
                        _ => {
                            v_t_1621_ = v_r_1626_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1631_ = lean_box(0);
                    return v___x_1631_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg___boxed(
    mut v_t_1632_: *mut LeanObject,
    mut v_k_1633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1634_: *mut LeanObject = core::ptr::null_mut();
    v_res_1634_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_t_1632_, v_k_1633_);
    lean_dec(v_k_1633_);
    lean_dec(v_t_1632_);
    return v_res_1634_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(
    mut v_package_1635_: *mut LeanObject,
    mut v_as_1636_: *mut LeanObject,
    mut v_sz_1637_: usize,
    mut v_i_1638_: usize,
    mut v_b_1639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1640_: u8 = 0;
    let mut v_a_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: u8 = 0;
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: usize = 0;
    let mut v___x_1647_: usize = 0;
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1640_ = lean_usize_dec_lt(v_i_1638_, v_sz_1637_);
                if v___x_1640_ == 0 {
                    lean_inc_ref(v_b_1639_);
                    return v_b_1639_;
                } else {
                    v_a_1641_ = lean_array_uget_borrowed(v_as_1636_, v_i_1638_);
                    v_baseName_1642_ = lean_ctor_get(v_a_1641_, 1);
                    v___x_1643_ = lean_box(0);
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
                        lean_inc(v_a_1641_);
                        v___x_1649_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1649_, 0, v_a_1641_);
                        v___x_1650_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1650_, 0, v___x_1649_);
                        v___x_1651_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1651_, 0, v___x_1650_);
                        lean_ctor_set(v___x_1651_, 1, v___x_1643_);
                        return v___x_1651_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1___boxed(
    mut v_package_1652_: *mut LeanObject,
    mut v_as_1653_: *mut LeanObject,
    mut v_sz_1654_: *mut LeanObject,
    mut v_i_1655_: *mut LeanObject,
    mut v_b_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1657_: usize = 0;
    let mut v_i_boxed_1658_: usize = 0;
    let mut v_res_1659_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1657_ = lean_unbox_usize(v_sz_1654_);
    lean_dec(v_sz_1654_);
    v_i_boxed_1658_ = lean_unbox_usize(v_i_1655_);
    lean_dec(v_i_1655_);
    v_res_1659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_1652_, v_as_1653_, v_sz_boxed_1657_, v_i_boxed_1658_, v_b_1656_);
    lean_dec_ref(v_b_1656_);
    lean_dec_ref(v_as_1653_);
    lean_dec(v_package_1652_);
    return v_res_1659_;
}
pub unsafe fn _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3()
-> *mut LeanObject {
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    v___x_1664_ =
        l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__2;
    v___x_1665_ = l_Lake_BuildTrace_nil(v___x_1664_);
    return v___x_1665_;
}
pub unsafe fn _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4()
-> *mut LeanObject {
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___x_1669_: u8 = 0;
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    v___x_1666_ = lean_unsigned_to_nat(0);
    v___x_1667_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
    v___x_1668_ = 0;
    v___x_1669_ = 0;
    v___x_1670_ =
        l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__0;
    v___x_1671_ = lean_alloc_ctor(0, 3, (2) as u32);
    lean_ctor_set(v___x_1671_, 0, v___x_1670_);
    lean_ctor_set(v___x_1671_, 1, v___x_1667_);
    lean_ctor_set(v___x_1671_, 2, v___x_1666_);
    lean_ctor_set_uint8(
        v___x_1671_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_1669_,
    );
    lean_ctor_set_uint8(
        v___x_1671_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
        v___x_1668_,
    );
    return v___x_1671_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux(
    mut v_defaultPkg_1682_: *mut LeanObject,
    mut v_root_1683_: *mut LeanObject,
    mut v_self_1684_: *mut LeanObject,
    mut v_facetless_1685_: u8,
    mut v_a_1686_: *mut LeanObject,
    mut v_a_1687_: *mut LeanObject,
    mut v_a_1688_: *mut LeanObject,
    mut v_a_1689_: *mut LeanObject,
    mut v_a_1690_: *mut LeanObject,
    mut v_a_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lib_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_package_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v_a_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: u8 = 0;
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packages_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1794_: usize = 0;
    let mut v___x_1795_: usize = 0;
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1800_: u8 = 0;
    let mut v_package_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v_a_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: u8 = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: u8 = 0;
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: u8 = 0;
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: u8 = 0;
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packageMap_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packages_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1881_: usize = 0;
    let mut v___x_1882_: usize = 0;
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1887_: u8 = 0;
    let mut v_package_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v_a_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keyName_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_a_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1928_: u8 = 0;
    let mut v___x_1929_: u8 = 0;
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1940_: u8 = 0;
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1946_: u8 = 0;
    let mut v_a_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut v_reuseFailAlloc_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1968_: u8 = 0;
    let mut v_a_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1973_: u8 = 0;
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1977_: u8 = 0;
    let mut v_isSharedCheck_1978_: u8 = 0;
    let mut v_unused_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: u8 = 0;
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: u8 = 0;
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packageMap_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: u8 = 0;
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packages_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2033_: usize = 0;
    let mut v___x_2034_: usize = 0;
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_target_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facet_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2044_: u8 = 0;
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v_a_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2055_: u8 = 0;
    let mut v_kind_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outKind_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: u8 = 0;
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: u8 = 0;
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: u8 = 0;
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2108_: u8 = 0;
    let mut v_unused_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_unused_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2112_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1705_ = l_Lake_instDataKindModule;
                match lean_obj_tag(v_self_1684_) {
                    0 => {
                        lean_dec_ref(v_a_1686_);
                        lean_dec_ref(v_defaultPkg_1682_);
                        v_module_1706_ = lean_ctor_get(v_self_1684_, 0);
                        lean_inc_n(v_module_1706_, 2);
                        lean_dec_ref_known(v_self_1684_, 1);
                        v_toContext_1707_ = lean_ctor_get(v_a_1690_, 1);
                        v___x_1708_ =
                            l_Lake_Workspace_findModule_x3f(v_module_1706_, v_toContext_1707_);
                        if lean_obj_tag(v___x_1708_) == 1 {
                            lean_dec_ref(v_root_1683_);
                            v_val_1709_ = lean_ctor_get(v___x_1708_, 0);
                            lean_inc(v_val_1709_);
                            lean_dec_ref_known(v___x_1708_, 1);
                            v_lib_1710_ = lean_ctor_get(v_val_1709_, 0);
                            v_pkg_1711_ = lean_ctor_get(v_lib_1710_, 0);
                            v_keyName_1712_ = lean_ctor_get(v_pkg_1711_, 2);
                            lean_inc(v_keyName_1712_);
                            v___x_1713_ = lean_alloc_ctor(2, 2, (0) as u32);
                            lean_ctor_set(v___x_1713_, 0, v_keyName_1712_);
                            lean_ctor_set(v___x_1713_, 1, v_module_1706_);
                            v___x_1714_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                            v___x_1715_ = 0;
                            v___x_1716_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                            v___x_1717_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1717_, 0, v_val_1709_);
                            lean_ctor_set(v___x_1717_, 1, v___x_1716_);
                            v___x_1718_ = lean_task_pure(v___x_1717_);
                            v___x_1719_ = lean_alloc_ctor(0, 3, (1) as u32);
                            lean_ctor_set(v___x_1719_, 0, v___x_1718_);
                            lean_ctor_set(v___x_1719_, 1, v___x_1705_);
                            lean_ctor_set(v___x_1719_, 2, v___x_1714_);
                            lean_ctor_set_uint8(
                                v___x_1719_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                                v___x_1715_,
                            );
                            v___x_1720_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1720_, 0, v___x_1713_);
                            lean_ctor_set(v___x_1720_, 1, v___x_1719_);
                            v___x_1721_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_1721_, 0, v___x_1720_);
                            lean_ctor_set(v___x_1721_, 1, v_a_1691_);
                            return v___x_1721_;
                        } else {
                            lean_dec(v___x_1708_);
                            v___x_1722_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                            v___x_1723_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                            v___x_1724_ = lean_string_append(v___x_1722_, v___x_1723_);
                            lean_dec_ref(v___x_1723_);
                            v___x_1725_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5;
                            v___x_1726_ = lean_string_append(v___x_1724_, v___x_1725_);
                            v___x_1727_ = 1;
                            v___x_1728_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_module_1706_,
                                    v___x_1727_,
                                );
                            v___x_1729_ = lean_string_append(v___x_1726_, v___x_1728_);
                            lean_dec_ref(v___x_1728_);
                            v___x_1730_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                            v___x_1731_ = lean_string_append(v___x_1729_, v___x_1730_);
                            v___x_1732_ = 3;
                            v___x_1733_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_1733_, 0, v___x_1731_);
                            lean_ctor_set_uint8(
                                v___x_1733_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_1732_,
                            );
                            v___x_1734_ = lean_array_get_size(v_a_1691_);
                            v___x_1735_ = lean_array_push(v_a_1691_, v___x_1733_);
                            v___x_1736_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_1736_, 0, v___x_1734_);
                            lean_ctor_set(v___x_1736_, 1, v___x_1735_);
                            return v___x_1736_;
                        }
                    }
                    1 => {
                        lean_dec_ref(v_a_1686_);
                        v_package_1737_ = lean_ctor_get(v_self_1684_, 0);
                        v_isSharedCheck_1800_ = (!lean_is_exclusive(v_self_1684_)) as u8;
                        if v_isSharedCheck_1800_ == 0 {
                            v___x_1739_ = v_self_1684_;
                            v_isShared_1740_ = v_isSharedCheck_1800_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_package_1737_);
                            lean_dec(v_self_1684_);
                            v___x_1739_ = lean_box(0);
                            v_isShared_1740_ = v_isSharedCheck_1800_;
                            state = 4;
                            continue;
                        }
                    }
                    2 => {
                        lean_dec_ref(v_a_1686_);
                        v_package_1801_ = lean_ctor_get(v_self_1684_, 0);
                        v_module_1802_ = lean_ctor_get(v_self_1684_, 1);
                        v_isSharedCheck_1887_ = (!lean_is_exclusive(v_self_1684_)) as u8;
                        if v_isSharedCheck_1887_ == 0 {
                            v___x_1804_ = v_self_1684_;
                            v_isShared_1805_ = v_isSharedCheck_1887_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_module_1802_);
                            lean_inc(v_package_1801_);
                            lean_dec(v_self_1684_);
                            v___x_1804_ = lean_box(0);
                            v_isShared_1805_ = v_isSharedCheck_1887_;
                            state = 8;
                            continue;
                        }
                    }
                    3 => {
                        v_package_1888_ = lean_ctor_get(v_self_1684_, 0);
                        v_target_1889_ = lean_ctor_get(v_self_1684_, 1);
                        v_isSharedCheck_2039_ = (!lean_is_exclusive(v_self_1684_)) as u8;
                        if v_isSharedCheck_2039_ == 0 {
                            v___x_1891_ = v_self_1684_;
                            v_isShared_1892_ = v_isSharedCheck_2039_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_target_1889_);
                            lean_inc(v_package_1888_);
                            lean_dec(v_self_1684_);
                            v___x_1891_ = lean_box(0);
                            v_isShared_1892_ = v_isSharedCheck_2039_;
                            state = 12;
                            continue;
                        }
                    }
                    _ => {
                        v_target_2040_ = lean_ctor_get(v_self_1684_, 0);
                        v_facet_2041_ = lean_ctor_get(v_self_1684_, 1);
                        v_isSharedCheck_2112_ = (!lean_is_exclusive(v_self_1684_)) as u8;
                        if v_isSharedCheck_2112_ == 0 {
                            v___x_2043_ = v_self_1684_;
                            v_isShared_2044_ = v_isSharedCheck_2112_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_facet_2041_);
                            lean_inc(v_target_2040_);
                            lean_dec(v_self_1684_);
                            v___x_2043_ = lean_box(0);
                            v_isShared_2044_ = v_isSharedCheck_2112_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1696_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1696_, 0, v_a_1694_);
                lean_ctor_set(v___x_1696_, 1, v_a_1695_);
                return v___x_1696_;
            }
            2 => {
                v___x_1700_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1700_, 0, v_a_1698_);
                lean_ctor_set(v___x_1700_, 1, v_a_1699_);
                return v___x_1700_;
            }
            3 => {
                v___x_1704_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1704_, 0, v_a_1702_);
                lean_ctor_set(v___x_1704_, 1, v_a_1703_);
                return v___x_1704_;
            }
            4 => {
                v___x_1757_ = l_Lake_instDataKindPackage;
                match lean_obj_tag(v_package_1737_) {
                    0 => {
                        lean_dec_ref(v_root_1683_);
                        v_a_1759_ = v_defaultPkg_1682_;
                        v_a_1760_ = v_a_1691_;
                        state = 6;
                        continue;
                    }
                    2 => {
                        lean_dec_ref(v_defaultPkg_1682_);
                        v_toContext_1773_ = lean_ctor_get(v_a_1690_, 1);
                        v_packageMap_1774_ = lean_ctor_get(v_toContext_1773_, 5);
                        v___x_1775_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_1774_, v_package_1737_);
                        if lean_obj_tag(v___x_1775_) == 1 {
                            lean_dec_ref_known(v_package_1737_, 2);
                            lean_dec_ref(v_root_1683_);
                            v_val_1776_ = lean_ctor_get(v___x_1775_, 0);
                            lean_inc(v_val_1776_);
                            lean_dec_ref_known(v___x_1775_, 1);
                            v_a_1759_ = v_val_1776_;
                            v_a_1760_ = v_a_1691_;
                            state = 6;
                            continue;
                        } else {
                            lean_dec(v___x_1775_);
                            lean_del_object(v___x_1739_);
                            v___x_1777_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                            v___x_1778_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                            v___x_1779_ = lean_string_append(v___x_1777_, v___x_1778_);
                            lean_dec_ref(v___x_1778_);
                            v___x_1780_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                            v___x_1781_ = lean_string_append(v___x_1779_, v___x_1780_);
                            v___x_1782_ = 1;
                            v___x_1783_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_package_1737_,
                                    v___x_1782_,
                                );
                            v___x_1784_ = lean_string_append(v___x_1781_, v___x_1783_);
                            lean_dec_ref(v___x_1783_);
                            v___x_1785_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                            v___x_1786_ = lean_string_append(v___x_1784_, v___x_1785_);
                            v___x_1787_ = 3;
                            v___x_1788_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_1788_, 0, v___x_1786_);
                            lean_ctor_set_uint8(
                                v___x_1788_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                        lean_dec_ref(v_defaultPkg_1682_);
                        v_toContext_1791_ = lean_ctor_get(v_a_1690_, 1);
                        v_packages_1792_ = lean_ctor_get(v_toContext_1791_, 4);
                        v___x_1793_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                        v_sz_1794_ = lean_array_size(v_packages_1792_);
                        v___x_1795_ = 0usize;
                        v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_1737_, v_packages_1792_, v_sz_1794_, v___x_1795_, v___x_1793_);
                        v_fst_1797_ = lean_ctor_get(v___x_1796_, 0);
                        lean_inc(v_fst_1797_);
                        lean_dec_ref(v___x_1796_);
                        if lean_obj_tag(v_fst_1797_) == 0 {
                            lean_del_object(v___x_1739_);
                            v_a_1742_ = v_a_1691_;
                            state = 5;
                            continue;
                        } else {
                            v_val_1798_ = lean_ctor_get(v_fst_1797_, 0);
                            lean_inc(v_val_1798_);
                            lean_dec_ref_known(v_fst_1797_, 1);
                            if lean_obj_tag(v_val_1798_) == 1 {
                                lean_dec(v_package_1737_);
                                lean_dec_ref(v_root_1683_);
                                v_val_1799_ = lean_ctor_get(v_val_1798_, 0);
                                lean_inc(v_val_1799_);
                                lean_dec_ref_known(v_val_1798_, 1);
                                v_a_1759_ = v_val_1799_;
                                v_a_1760_ = v_a_1691_;
                                state = 6;
                                continue;
                            } else {
                                lean_dec(v_val_1798_);
                                lean_del_object(v___x_1739_);
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
                lean_dec_ref(v___x_1744_);
                v___x_1746_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                v___x_1747_ = lean_string_append(v___x_1745_, v___x_1746_);
                v___x_1748_ = 1;
                v___x_1749_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_package_1737_,
                    v___x_1748_,
                );
                v___x_1750_ = lean_string_append(v___x_1747_, v___x_1749_);
                lean_dec_ref(v___x_1749_);
                v___x_1751_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                v___x_1752_ = lean_string_append(v___x_1750_, v___x_1751_);
                v___x_1753_ = 3;
                v___x_1754_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_1754_, 0, v___x_1752_);
                lean_ctor_set_uint8(
                    v___x_1754_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                v_keyName_1761_ = lean_ctor_get(v_a_1759_, 2);
                lean_inc(v_keyName_1761_);
                if v_isShared_1740_ == 0 {
                    lean_ctor_set(v___x_1739_, 0, v_keyName_1761_);
                    v___x_1763_ = v___x_1739_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_keyName_1761_);
                    v___x_1763_ = v_reuseFailAlloc_1772_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1764_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                v___x_1765_ = 0;
                v___x_1766_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                v___x_1767_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1767_, 0, v_a_1759_);
                lean_ctor_set(v___x_1767_, 1, v___x_1766_);
                v___x_1768_ = lean_task_pure(v___x_1767_);
                v___x_1769_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_1769_, 0, v___x_1768_);
                lean_ctor_set(v___x_1769_, 1, v___x_1757_);
                lean_ctor_set(v___x_1769_, 2, v___x_1764_);
                lean_ctor_set_uint8(
                    v___x_1769_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1765_,
                );
                v___x_1770_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1770_, 0, v___x_1763_);
                lean_ctor_set(v___x_1770_, 1, v___x_1769_);
                v___x_1771_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1771_, 0, v___x_1770_);
                lean_ctor_set(v___x_1771_, 1, v_a_1760_);
                return v___x_1771_;
            }
            8 => match lean_obj_tag(v_package_1801_) {
                0 => {
                    v_a_1807_ = v_defaultPkg_1682_;
                    v_a_1808_ = v_a_1691_;
                    state = 9;
                    continue;
                }
                2 => {
                    lean_dec_ref(v_defaultPkg_1682_);
                    v_toContext_1860_ = lean_ctor_get(v_a_1690_, 1);
                    v_packageMap_1861_ = lean_ctor_get(v_toContext_1860_, 5);
                    v___x_1862_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_1861_, v_package_1801_);
                    if lean_obj_tag(v___x_1862_) == 1 {
                        lean_dec_ref_known(v_package_1801_, 2);
                        v_val_1863_ = lean_ctor_get(v___x_1862_, 0);
                        lean_inc(v_val_1863_);
                        lean_dec_ref_known(v___x_1862_, 1);
                        v_a_1807_ = v_val_1863_;
                        v_a_1808_ = v_a_1691_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v___x_1862_);
                        lean_del_object(v___x_1804_);
                        lean_dec(v_module_1802_);
                        v___x_1864_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_1865_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                        v___x_1866_ = lean_string_append(v___x_1864_, v___x_1865_);
                        lean_dec_ref(v___x_1865_);
                        v___x_1867_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                        v___x_1868_ = lean_string_append(v___x_1866_, v___x_1867_);
                        v___x_1869_ = 1;
                        v___x_1870_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_package_1801_,
                                v___x_1869_,
                            );
                        v___x_1871_ = lean_string_append(v___x_1868_, v___x_1870_);
                        lean_dec_ref(v___x_1870_);
                        v___x_1872_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                        v___x_1873_ = lean_string_append(v___x_1871_, v___x_1872_);
                        v___x_1874_ = 3;
                        v___x_1875_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1875_, 0, v___x_1873_);
                        lean_ctor_set_uint8(
                            v___x_1875_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                    lean_dec_ref(v_defaultPkg_1682_);
                    v_toContext_1878_ = lean_ctor_get(v_a_1690_, 1);
                    v_packages_1879_ = lean_ctor_get(v_toContext_1878_, 4);
                    v___x_1880_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                    v_sz_1881_ = lean_array_size(v_packages_1879_);
                    v___x_1882_ = 0usize;
                    v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_1801_, v_packages_1879_, v_sz_1881_, v___x_1882_, v___x_1880_);
                    v_fst_1884_ = lean_ctor_get(v___x_1883_, 0);
                    lean_inc(v_fst_1884_);
                    lean_dec_ref(v___x_1883_);
                    if lean_obj_tag(v_fst_1884_) == 0 {
                        lean_del_object(v___x_1804_);
                        lean_dec(v_module_1802_);
                        v_a_1845_ = v_a_1691_;
                        state = 11;
                        continue;
                    } else {
                        v_val_1885_ = lean_ctor_get(v_fst_1884_, 0);
                        lean_inc(v_val_1885_);
                        lean_dec_ref_known(v_fst_1884_, 1);
                        if lean_obj_tag(v_val_1885_) == 1 {
                            lean_dec(v_package_1801_);
                            v_val_1886_ = lean_ctor_get(v_val_1885_, 0);
                            lean_inc(v_val_1886_);
                            lean_dec_ref_known(v_val_1885_, 1);
                            v_a_1807_ = v_val_1886_;
                            v_a_1808_ = v_a_1691_;
                            state = 9;
                            continue;
                        } else {
                            lean_dec(v_val_1885_);
                            lean_del_object(v___x_1804_);
                            lean_dec(v_module_1802_);
                            v_a_1845_ = v_a_1691_;
                            state = 11;
                            continue;
                        }
                    }
                }
            },
            9 => {
                lean_inc_ref(v_a_1807_);
                lean_inc(v_module_1802_);
                v___x_1809_ = l_Lake_Package_findTargetModule_x3f(v_module_1802_, v_a_1807_);
                if lean_obj_tag(v___x_1809_) == 1 {
                    lean_dec_ref(v_root_1683_);
                    v_val_1810_ = lean_ctor_get(v___x_1809_, 0);
                    lean_inc(v_val_1810_);
                    lean_dec_ref_known(v___x_1809_, 1);
                    v_keyName_1811_ = lean_ctor_get(v_a_1807_, 2);
                    lean_inc(v_keyName_1811_);
                    lean_dec_ref(v_a_1807_);
                    if v_isShared_1805_ == 0 {
                        lean_ctor_set(v___x_1804_, 0, v_keyName_1811_);
                        v___x_1813_ = v___x_1804_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1822_ = lean_alloc_ctor(2, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_keyName_1811_);
                        lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_module_1802_);
                        v___x_1813_ = v_reuseFailAlloc_1822_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1809_);
                    lean_del_object(v___x_1804_);
                    v_baseName_1823_ = lean_ctor_get(v_a_1807_, 1);
                    lean_inc(v_baseName_1823_);
                    lean_dec_ref(v_a_1807_);
                    v___x_1824_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_1825_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                    v___x_1826_ = lean_string_append(v___x_1824_, v___x_1825_);
                    lean_dec_ref(v___x_1825_);
                    v___x_1827_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__6;
                    v___x_1828_ = lean_string_append(v___x_1826_, v___x_1827_);
                    v___x_1829_ = 1;
                    v___x_1830_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_module_1802_,
                        v___x_1829_,
                    );
                    v___x_1831_ = lean_string_append(v___x_1828_, v___x_1830_);
                    lean_dec_ref(v___x_1830_);
                    v___x_1832_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7;
                    v___x_1833_ = lean_string_append(v___x_1831_, v___x_1832_);
                    v___x_1834_ = 0;
                    v___x_1835_ = l_Lean_Name_toString(v_baseName_1823_, v___x_1834_);
                    v___x_1836_ = lean_string_append(v___x_1833_, v___x_1835_);
                    lean_dec_ref(v___x_1835_);
                    v___x_1837_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                    v___x_1838_ = lean_string_append(v___x_1836_, v___x_1837_);
                    v___x_1839_ = 3;
                    v___x_1840_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_1840_, 0, v___x_1838_);
                    lean_ctor_set_uint8(
                        v___x_1840_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1839_,
                    );
                    v___x_1841_ = lean_array_get_size(v_a_1808_);
                    v___x_1842_ = lean_array_push(v_a_1808_, v___x_1840_);
                    v___x_1843_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1843_, 0, v___x_1841_);
                    lean_ctor_set(v___x_1843_, 1, v___x_1842_);
                    return v___x_1843_;
                }
            }
            10 => {
                v___x_1814_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                v___x_1815_ = 0;
                v___x_1816_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                v___x_1817_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1817_, 0, v_val_1810_);
                lean_ctor_set(v___x_1817_, 1, v___x_1816_);
                v___x_1818_ = lean_task_pure(v___x_1817_);
                v___x_1819_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_1819_, 0, v___x_1818_);
                lean_ctor_set(v___x_1819_, 1, v___x_1705_);
                lean_ctor_set(v___x_1819_, 2, v___x_1814_);
                lean_ctor_set_uint8(
                    v___x_1819_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1815_,
                );
                v___x_1820_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1820_, 0, v___x_1813_);
                lean_ctor_set(v___x_1820_, 1, v___x_1819_);
                v___x_1821_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1821_, 0, v___x_1820_);
                lean_ctor_set(v___x_1821_, 1, v_a_1808_);
                return v___x_1821_;
            }
            11 => {
                v___x_1846_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                v___x_1847_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                v___x_1848_ = lean_string_append(v___x_1846_, v___x_1847_);
                lean_dec_ref(v___x_1847_);
                v___x_1849_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                v___x_1850_ = lean_string_append(v___x_1848_, v___x_1849_);
                v___x_1851_ = 1;
                v___x_1852_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_package_1801_,
                    v___x_1851_,
                );
                v___x_1853_ = lean_string_append(v___x_1850_, v___x_1852_);
                lean_dec_ref(v___x_1852_);
                v___x_1854_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                v___x_1855_ = lean_string_append(v___x_1853_, v___x_1854_);
                v___x_1856_ = 3;
                v___x_1857_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_1857_, 0, v___x_1855_);
                lean_ctor_set_uint8(
                    v___x_1857_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1856_,
                );
                v___x_1858_ = lean_array_get_size(v_a_1845_);
                v___x_1859_ = lean_array_push(v_a_1845_, v___x_1857_);
                v_a_1698_ = v___x_1858_;
                v_a_1699_ = v___x_1859_;
                state = 2;
                continue;
            }
            12 => match lean_obj_tag(v_package_1888_) {
                0 => {
                    v_a_1894_ = v_defaultPkg_1682_;
                    v_a_1895_ = v_a_1691_;
                    state = 13;
                    continue;
                }
                2 => {
                    lean_dec_ref(v_defaultPkg_1682_);
                    v_toContext_2012_ = lean_ctor_get(v_a_1690_, 1);
                    v_packageMap_2013_ = lean_ctor_get(v_toContext_2012_, 5);
                    v___x_2014_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_2013_, v_package_1888_);
                    if lean_obj_tag(v___x_2014_) == 1 {
                        lean_dec_ref_known(v_package_1888_, 2);
                        v_val_2015_ = lean_ctor_get(v___x_2014_, 0);
                        lean_inc(v_val_2015_);
                        lean_dec_ref_known(v___x_2014_, 1);
                        v_a_1894_ = v_val_2015_;
                        v_a_1895_ = v_a_1691_;
                        state = 13;
                        continue;
                    } else {
                        lean_dec(v___x_2014_);
                        lean_del_object(v___x_1891_);
                        lean_dec(v_target_1889_);
                        lean_dec_ref(v_a_1686_);
                        v___x_2016_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_2017_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                        v___x_2018_ = lean_string_append(v___x_2016_, v___x_2017_);
                        lean_dec_ref(v___x_2017_);
                        v___x_2019_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                        v___x_2020_ = lean_string_append(v___x_2018_, v___x_2019_);
                        v___x_2021_ = 1;
                        v___x_2022_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_package_1888_,
                                v___x_2021_,
                            );
                        v___x_2023_ = lean_string_append(v___x_2020_, v___x_2022_);
                        lean_dec_ref(v___x_2022_);
                        v___x_2024_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                        v___x_2025_ = lean_string_append(v___x_2023_, v___x_2024_);
                        v___x_2026_ = 3;
                        v___x_2027_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_2027_, 0, v___x_2025_);
                        lean_ctor_set_uint8(
                            v___x_2027_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                    lean_dec_ref(v_defaultPkg_1682_);
                    v_toContext_2030_ = lean_ctor_get(v_a_1690_, 1);
                    v_packages_2031_ = lean_ctor_get(v_toContext_2030_, 4);
                    v___x_2032_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__14;
                    v_sz_2033_ = lean_array_size(v_packages_2031_);
                    v___x_2034_ = 0usize;
                    v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__1(v_package_1888_, v_packages_2031_, v_sz_2033_, v___x_2034_, v___x_2032_);
                    v_fst_2036_ = lean_ctor_get(v___x_2035_, 0);
                    lean_inc(v_fst_2036_);
                    lean_dec_ref(v___x_2035_);
                    if lean_obj_tag(v_fst_2036_) == 0 {
                        lean_del_object(v___x_1891_);
                        lean_dec(v_target_1889_);
                        lean_dec_ref(v_a_1686_);
                        v_a_1997_ = v_a_1691_;
                        state = 29;
                        continue;
                    } else {
                        v_val_2037_ = lean_ctor_get(v_fst_2036_, 0);
                        lean_inc(v_val_2037_);
                        lean_dec_ref_known(v_fst_2036_, 1);
                        if lean_obj_tag(v_val_2037_) == 1 {
                            lean_dec(v_package_1888_);
                            v_val_2038_ = lean_ctor_get(v_val_2037_, 0);
                            lean_inc(v_val_2038_);
                            lean_dec_ref_known(v_val_2037_, 1);
                            v_a_1894_ = v_val_2038_;
                            v_a_1895_ = v_a_1691_;
                            state = 13;
                            continue;
                        } else {
                            lean_dec(v_val_2037_);
                            lean_del_object(v___x_1891_);
                            lean_dec(v_target_1889_);
                            lean_dec_ref(v_a_1686_);
                            v_a_1997_ = v_a_1691_;
                            state = 29;
                            continue;
                        }
                    }
                }
            },
            13 => {
                v_baseName_1896_ = lean_ctor_get(v_a_1894_, 1);
                v_keyName_1897_ = lean_ctor_get(v_a_1894_, 2);
                lean_inc(v_target_1889_);
                lean_inc(v_keyName_1897_);
                if v_isShared_1892_ == 0 {
                    lean_ctor_set(v___x_1891_, 0, v_keyName_1897_);
                    v___x_1899_ = v___x_1891_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1995_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_keyName_1897_);
                    lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_target_1889_);
                    v___x_1899_ = v_reuseFailAlloc_1995_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_facetless_1685_ == 0 {
                    lean_dec_ref(v_root_1683_);
                    v___x_1900_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1900_, 0, v_a_1894_);
                    lean_ctor_set(v___x_1900_, 1, v_target_1889_);
                    lean_inc_ref(v_a_1690_);
                    lean_inc(v_a_1689_);
                    lean_inc(v_a_1688_);
                    lean_inc(v_a_1687_);
                    v___x_1901_ = lean_apply_7(
                        v_a_1686_,
                        v___x_1900_,
                        v_a_1687_,
                        v_a_1688_,
                        v_a_1689_,
                        v_a_1690_,
                        v_a_1895_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1901_) == 0 {
                        v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
                        v_a_1903_ = lean_ctor_get(v___x_1901_, 1);
                        v_isSharedCheck_1911_ = (!lean_is_exclusive(v___x_1901_)) as u8;
                        if v_isSharedCheck_1911_ == 0 {
                            v___x_1905_ = v___x_1901_;
                            v_isShared_1906_ = v_isSharedCheck_1911_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_1903_);
                            lean_inc(v_a_1902_);
                            lean_dec(v___x_1901_);
                            v___x_1905_ = lean_box(0);
                            v_isShared_1906_ = v_isSharedCheck_1911_;
                            state = 15;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1899_);
                        v_a_1912_ = lean_ctor_get(v___x_1901_, 0);
                        v_a_1913_ = lean_ctor_get(v___x_1901_, 1);
                        v_isSharedCheck_1920_ = (!lean_is_exclusive(v___x_1901_)) as u8;
                        if v_isSharedCheck_1920_ == 0 {
                            v___x_1915_ = v___x_1901_;
                            v_isShared_1916_ = v_isSharedCheck_1920_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_1913_);
                            lean_inc(v_a_1912_);
                            lean_dec(v___x_1901_);
                            v___x_1915_ = lean_box(0);
                            v_isShared_1916_ = v_isSharedCheck_1920_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    v___x_1921_ = l_Lake_Package_findTargetDecl_x3f(v_target_1889_, v_a_1894_);
                    if lean_obj_tag(v___x_1921_) == 1 {
                        lean_dec_ref(v_root_1683_);
                        v_val_1922_ = lean_ctor_get(v___x_1921_, 0);
                        lean_inc(v_val_1922_);
                        lean_dec_ref_known(v___x_1921_, 1);
                        v_name_1923_ = lean_ctor_get(v_val_1922_, 1);
                        v_kind_1924_ = lean_ctor_get(v_val_1922_, 2);
                        v_config_1925_ = lean_ctor_get(v_val_1922_, 3);
                        v_isSharedCheck_1978_ = (!lean_is_exclusive(v_val_1922_)) as u8;
                        if v_isSharedCheck_1978_ == 0 {
                            v_unused_1979_ = lean_ctor_get(v_val_1922_, 0);
                            lean_dec(v_unused_1979_);
                            v___x_1927_ = v_val_1922_;
                            v_isShared_1928_ = v_isSharedCheck_1978_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_config_1925_);
                            lean_inc(v_kind_1924_);
                            lean_inc(v_name_1923_);
                            lean_dec(v_val_1922_);
                            v___x_1927_ = lean_box(0);
                            v_isShared_1928_ = v_isSharedCheck_1978_;
                            state = 19;
                            continue;
                        }
                    } else {
                        lean_inc(v_baseName_1896_);
                        lean_dec(v___x_1921_);
                        lean_dec_ref(v___x_1899_);
                        lean_dec_ref(v_a_1894_);
                        lean_dec(v_target_1889_);
                        lean_dec_ref(v_a_1686_);
                        v___x_1980_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_1981_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                        v___x_1982_ = lean_string_append(v___x_1980_, v___x_1981_);
                        lean_dec_ref(v___x_1981_);
                        v___x_1983_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__10;
                        v___x_1984_ = lean_string_append(v___x_1982_, v___x_1983_);
                        v___x_1985_ = 0;
                        v___x_1986_ = l_Lean_Name_toString(v_baseName_1896_, v___x_1985_);
                        v___x_1987_ = lean_string_append(v___x_1984_, v___x_1986_);
                        lean_dec_ref(v___x_1986_);
                        v___x_1988_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                        v___x_1989_ = lean_string_append(v___x_1987_, v___x_1988_);
                        v___x_1990_ = 3;
                        v___x_1991_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_1991_, 0, v___x_1989_);
                        lean_ctor_set_uint8(
                            v___x_1991_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_1990_,
                        );
                        v___x_1992_ = lean_array_get_size(v_a_1895_);
                        v___x_1993_ = lean_array_push(v_a_1895_, v___x_1991_);
                        v___x_1994_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1994_, 0, v___x_1992_);
                        lean_ctor_set(v___x_1994_, 1, v___x_1993_);
                        return v___x_1994_;
                    }
                }
            }
            15 => {
                v___x_1907_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1907_, 0, v___x_1899_);
                lean_ctor_set(v___x_1907_, 1, v_a_1902_);
                if v_isShared_1906_ == 0 {
                    lean_ctor_set(v___x_1905_, 0, v___x_1907_);
                    v___x_1909_ = v___x_1905_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
                    lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_a_1903_);
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
                    v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1912_);
                    lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_a_1913_);
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
                    lean_dec(v_target_1889_);
                    v___x_1930_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__9;
                    lean_inc(v_kind_1924_);
                    v___x_1931_ = l_Lean_Name_str___override(v_kind_1924_, v___x_1930_);
                    v___x_1932_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1932_, 0, v_a_1894_);
                    lean_ctor_set(v___x_1932_, 1, v_name_1923_);
                    lean_ctor_set(v___x_1932_, 2, v_config_1925_);
                    lean_inc(v___x_1931_);
                    lean_inc_ref(v___x_1899_);
                    if v_isShared_1928_ == 0 {
                        lean_ctor_set_tag(v___x_1927_, 1);
                        lean_ctor_set(v___x_1927_, 3, v___x_1931_);
                        lean_ctor_set(v___x_1927_, 2, v___x_1932_);
                        lean_ctor_set(v___x_1927_, 1, v_kind_1924_);
                        lean_ctor_set(v___x_1927_, 0, v___x_1899_);
                        v___x_1934_ = v___x_1927_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 4, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1899_);
                        lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_kind_1924_);
                        lean_ctor_set(v_reuseFailAlloc_1956_, 2, v___x_1932_);
                        lean_ctor_set(v_reuseFailAlloc_1956_, 3, v___x_1931_);
                        v___x_1934_ = v_reuseFailAlloc_1956_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1927_);
                    lean_dec(v_config_1925_);
                    lean_dec(v_kind_1924_);
                    lean_dec(v_name_1923_);
                    v___x_1957_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1957_, 0, v_a_1894_);
                    lean_ctor_set(v___x_1957_, 1, v_target_1889_);
                    lean_inc_ref(v_a_1690_);
                    lean_inc(v_a_1689_);
                    lean_inc(v_a_1688_);
                    lean_inc(v_a_1687_);
                    v___x_1958_ = lean_apply_7(
                        v_a_1686_,
                        v___x_1957_,
                        v_a_1687_,
                        v_a_1688_,
                        v_a_1689_,
                        v_a_1690_,
                        v_a_1895_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1958_) == 0 {
                        v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
                        v_a_1960_ = lean_ctor_get(v___x_1958_, 1);
                        v_isSharedCheck_1968_ = (!lean_is_exclusive(v___x_1958_)) as u8;
                        if v_isSharedCheck_1968_ == 0 {
                            v___x_1962_ = v___x_1958_;
                            v_isShared_1963_ = v_isSharedCheck_1968_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_1960_);
                            lean_inc(v_a_1959_);
                            lean_dec(v___x_1958_);
                            v___x_1962_ = lean_box(0);
                            v_isShared_1963_ = v_isSharedCheck_1968_;
                            state = 25;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1899_);
                        v_a_1969_ = lean_ctor_get(v___x_1958_, 0);
                        v_a_1970_ = lean_ctor_get(v___x_1958_, 1);
                        v_isSharedCheck_1977_ = (!lean_is_exclusive(v___x_1958_)) as u8;
                        if v_isSharedCheck_1977_ == 0 {
                            v___x_1972_ = v___x_1958_;
                            v_isShared_1973_ = v_isSharedCheck_1977_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_1970_);
                            lean_inc(v_a_1969_);
                            lean_dec(v___x_1958_);
                            v___x_1972_ = lean_box(0);
                            v_isShared_1973_ = v_isSharedCheck_1977_;
                            state = 27;
                            continue;
                        }
                    }
                }
            }
            20 => {
                lean_inc_ref(v_a_1690_);
                lean_inc(v_a_1689_);
                lean_inc(v_a_1688_);
                lean_inc(v_a_1687_);
                v___x_1935_ = lean_apply_7(
                    v_a_1686_,
                    v___x_1934_,
                    v_a_1687_,
                    v_a_1688_,
                    v_a_1689_,
                    v_a_1690_,
                    v_a_1895_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1935_) == 0 {
                    v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
                    v_a_1937_ = lean_ctor_get(v___x_1935_, 1);
                    v_isSharedCheck_1946_ = (!lean_is_exclusive(v___x_1935_)) as u8;
                    if v_isSharedCheck_1946_ == 0 {
                        v___x_1939_ = v___x_1935_;
                        v_isShared_1940_ = v_isSharedCheck_1946_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_1937_);
                        lean_inc(v_a_1936_);
                        lean_dec(v___x_1935_);
                        v___x_1939_ = lean_box(0);
                        v_isShared_1940_ = v_isSharedCheck_1946_;
                        state = 21;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1931_);
                    lean_dec_ref(v___x_1899_);
                    v_a_1947_ = lean_ctor_get(v___x_1935_, 0);
                    v_a_1948_ = lean_ctor_get(v___x_1935_, 1);
                    v_isSharedCheck_1955_ = (!lean_is_exclusive(v___x_1935_)) as u8;
                    if v_isSharedCheck_1955_ == 0 {
                        v___x_1950_ = v___x_1935_;
                        v_isShared_1951_ = v_isSharedCheck_1955_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_1948_);
                        lean_inc(v_a_1947_);
                        lean_dec(v___x_1935_);
                        v___x_1950_ = lean_box(0);
                        v_isShared_1951_ = v_isSharedCheck_1955_;
                        state = 23;
                        continue;
                    }
                }
            }
            21 => {
                v___x_1941_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1941_, 0, v___x_1899_);
                lean_ctor_set(v___x_1941_, 1, v___x_1931_);
                v___x_1942_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1942_, 0, v___x_1941_);
                lean_ctor_set(v___x_1942_, 1, v_a_1936_);
                if v_isShared_1940_ == 0 {
                    lean_ctor_set(v___x_1939_, 0, v___x_1942_);
                    v___x_1944_ = v___x_1939_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
                    lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_a_1937_);
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
                    v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1947_);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_a_1948_);
                    v___x_1953_ = v_reuseFailAlloc_1954_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1953_;
            }
            25 => {
                v___x_1964_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1964_, 0, v___x_1899_);
                lean_ctor_set(v___x_1964_, 1, v_a_1959_);
                if v_isShared_1963_ == 0 {
                    lean_ctor_set(v___x_1962_, 0, v___x_1964_);
                    v___x_1966_ = v___x_1962_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
                    lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_a_1960_);
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
                    v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1969_);
                    lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_a_1970_);
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
                lean_dec_ref(v___x_1999_);
                v___x_2001_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                v___x_2002_ = lean_string_append(v___x_2000_, v___x_2001_);
                v___x_2003_ = 1;
                v___x_2004_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_package_1888_,
                    v___x_2003_,
                );
                v___x_2005_ = lean_string_append(v___x_2002_, v___x_2004_);
                lean_dec_ref(v___x_2004_);
                v___x_2006_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                v___x_2007_ = lean_string_append(v___x_2005_, v___x_2006_);
                v___x_2008_ = 3;
                v___x_2009_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_2009_, 0, v___x_2007_);
                lean_ctor_set_uint8(
                    v___x_2009_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
                lean_inc_ref(v_a_1686_);
                lean_inc_ref(v_target_2040_);
                lean_inc_ref(v_root_1683_);
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
                if lean_obj_tag(v___x_2046_) == 0 {
                    v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
                    lean_inc(v_a_2047_);
                    v_snd_2048_ = lean_ctor_get(v_a_2047_, 1);
                    v_isSharedCheck_2110_ = (!lean_is_exclusive(v_a_2047_)) as u8;
                    if v_isSharedCheck_2110_ == 0 {
                        v_unused_2111_ = lean_ctor_get(v_a_2047_, 0);
                        lean_dec(v_unused_2111_);
                        v___x_2050_ = v_a_2047_;
                        v_isShared_2051_ = v_isSharedCheck_2110_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_snd_2048_);
                        lean_dec(v_a_2047_);
                        v___x_2050_ = lean_box(0);
                        v_isShared_2051_ = v_isSharedCheck_2110_;
                        state = 31;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2043_);
                    lean_dec(v_facet_2041_);
                    lean_dec_ref(v_target_2040_);
                    lean_dec_ref(v_a_1686_);
                    lean_dec_ref(v_root_1683_);
                    return v___x_2046_;
                }
            }
            31 => {
                v_a_2052_ = lean_ctor_get(v___x_2046_, 1);
                v_isSharedCheck_2108_ = (!lean_is_exclusive(v___x_2046_)) as u8;
                if v_isSharedCheck_2108_ == 0 {
                    v_unused_2109_ = lean_ctor_get(v___x_2046_, 0);
                    lean_dec(v_unused_2109_);
                    v___x_2054_ = v___x_2046_;
                    v_isShared_2055_ = v_isSharedCheck_2108_;
                    state = 32;
                    continue;
                } else {
                    lean_inc(v_a_2052_);
                    lean_dec(v___x_2046_);
                    v___x_2054_ = lean_box(0);
                    v_isShared_2055_ = v_isSharedCheck_2108_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v_kind_2056_ = lean_ctor_get(v_snd_2048_, 1);
                v___x_2095_ = l_Lean_Name_isAnonymous(v_kind_2056_);
                if v___x_2095_ == 0 {
                    v___x_2096_ = l_Lean_Name_isAnonymous(v_facet_2041_);
                    if v___x_2096_ == 0 {
                        v___y_2058_ = v_facet_2041_;
                        state = 33;
                        continue;
                    } else {
                        lean_dec(v_facet_2041_);
                        v___x_2097_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__12;
                        v___y_2058_ = v___x_2097_;
                        state = 33;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2054_);
                    lean_del_object(v___x_2050_);
                    lean_dec(v_snd_2048_);
                    lean_del_object(v___x_2043_);
                    lean_dec(v_facet_2041_);
                    lean_dec_ref(v_target_2040_);
                    lean_dec_ref(v_a_1686_);
                    v___x_2098_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_2099_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                    v___x_2100_ = lean_string_append(v___x_2098_, v___x_2099_);
                    lean_dec_ref(v___x_2099_);
                    v___x_2101_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13;
                    v___x_2102_ = lean_string_append(v___x_2100_, v___x_2101_);
                    v___x_2103_ = 3;
                    v___x_2104_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2104_, 0, v___x_2102_);
                    lean_ctor_set_uint8(
                        v___x_2104_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2103_,
                    );
                    v___x_2105_ = lean_array_get_size(v_a_2052_);
                    v___x_2106_ = lean_array_push(v_a_2052_, v___x_2104_);
                    v___x_2107_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2107_, 0, v___x_2105_);
                    lean_ctor_set(v___x_2107_, 1, v___x_2106_);
                    return v___x_2107_;
                }
            }
            33 => {
                v_toContext_2059_ = lean_ctor_get(v_a_1690_, 1);
                v_facetConfigs_2060_ = lean_ctor_get(v_toContext_2059_, 6);
                lean_inc(v_kind_2056_);
                v___x_2061_ = l_Lean_Name_append(v_kind_2056_, v___y_2058_);
                v___x_2062_ = l_Lake_FacetConfigMap_get_x3f(v___x_2061_, v_facetConfigs_2060_);
                if lean_obj_tag(v___x_2062_) == 1 {
                    lean_dec_ref(v_root_1683_);
                    v_val_2063_ = lean_ctor_get(v___x_2062_, 0);
                    lean_inc(v_val_2063_);
                    lean_dec_ref_known(v___x_2062_, 1);
                    v_outKind_2064_ = lean_ctor_get(v_val_2063_, 2);
                    lean_inc(v_outKind_2064_);
                    lean_dec(v_val_2063_);
                    lean_inc(v___x_2061_);
                    lean_inc(v_kind_2056_);
                    lean_inc_ref(v_target_2040_);
                    v___f_2065_ = lean_alloc_closure(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___lam__0___boxed as *mut core::ffi::c_void, 11, 3);
                    lean_closure_set(v___f_2065_, 0, v_target_2040_);
                    lean_closure_set(v___f_2065_, 1, v_kind_2056_);
                    lean_closure_set(v___f_2065_, 2, v___x_2061_);
                    v___x_2066_ = lean_unsigned_to_nat(0);
                    v___x_2067_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
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
                        lean_ctor_set(v___x_2043_, 1, v___x_2061_);
                        v___x_2070_ = v___x_2043_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_2077_ = lean_alloc_ctor(4, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_target_2040_);
                        lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2061_);
                        v___x_2070_ = v_reuseFailAlloc_2077_;
                        state = 34;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2062_);
                    lean_del_object(v___x_2050_);
                    lean_dec(v_snd_2048_);
                    lean_del_object(v___x_2043_);
                    lean_dec_ref(v_target_2040_);
                    lean_dec_ref(v_a_1686_);
                    v___x_2078_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_2079_ = l_Lake_PartialBuildKey_toString(v_root_1683_);
                    v___x_2080_ = lean_string_append(v___x_2078_, v___x_2079_);
                    lean_dec_ref(v___x_2079_);
                    v___x_2081_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11;
                    v___x_2082_ = lean_string_append(v___x_2080_, v___x_2081_);
                    v___x_2083_ = 1;
                    v___x_2084_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___x_2061_,
                        v___x_2083_,
                    );
                    v___x_2085_ = lean_string_append(v___x_2082_, v___x_2084_);
                    lean_dec_ref(v___x_2084_);
                    v___x_2086_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                    v___x_2087_ = lean_string_append(v___x_2085_, v___x_2086_);
                    v___x_2088_ = 3;
                    v___x_2089_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2089_, 0, v___x_2087_);
                    lean_ctor_set_uint8(
                        v___x_2089_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2088_,
                    );
                    v___x_2090_ = lean_array_get_size(v_a_2052_);
                    v___x_2091_ = lean_array_push(v_a_2052_, v___x_2089_);
                    if v_isShared_2055_ == 0 {
                        lean_ctor_set_tag(v___x_2054_, 1);
                        lean_ctor_set(v___x_2054_, 1, v___x_2091_);
                        lean_ctor_set(v___x_2054_, 0, v___x_2090_);
                        v___x_2093_ = v___x_2054_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2090_);
                        lean_ctor_set(v_reuseFailAlloc_2094_, 1, v___x_2091_);
                        v___x_2093_ = v_reuseFailAlloc_2094_;
                        state = 37;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_2051_ == 0 {
                    lean_ctor_set(v___x_2050_, 1, v___x_2068_);
                    lean_ctor_set(v___x_2050_, 0, v___x_2070_);
                    v___x_2072_ = v___x_2050_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2070_);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___x_2068_);
                    v___x_2072_ = v_reuseFailAlloc_2076_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_2055_ == 0 {
                    lean_ctor_set(v___x_2054_, 0, v___x_2072_);
                    v___x_2074_ = v___x_2054_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
                    lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_a_2052_);
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
    mut v_defaultPkg_2113_: *mut LeanObject,
    mut v_root_2114_: *mut LeanObject,
    mut v_self_2115_: *mut LeanObject,
    mut v_facetless_2116_: *mut LeanObject,
    mut v_a_2117_: *mut LeanObject,
    mut v_a_2118_: *mut LeanObject,
    mut v_a_2119_: *mut LeanObject,
    mut v_a_2120_: *mut LeanObject,
    mut v_a_2121_: *mut LeanObject,
    mut v_a_2122_: *mut LeanObject,
    mut v_a_2123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_facetless_boxed_2124_: u8 = 0;
    let mut v_res_2125_: *mut LeanObject = core::ptr::null_mut();
    v_facetless_boxed_2124_ = (lean_unbox(v_facetless_2116_) as u8);
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
    lean_dec_ref(v_a_2121_);
    lean_dec(v_a_2120_);
    lean_dec(v_a_2119_);
    lean_dec(v_a_2118_);
    return v_res_2125_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(
    mut v_00_u03b2_2126_: *mut LeanObject,
    mut v_inst_2127_: *mut LeanObject,
    mut v_t_2128_: *mut LeanObject,
    mut v_k_2129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    v___x_2130_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_t_2128_, v_k_2129_);
    return v___x_2130_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___boxed(
    mut v_00_u03b2_2131_: *mut LeanObject,
    mut v_inst_2132_: *mut LeanObject,
    mut v_t_2133_: *mut LeanObject,
    mut v_k_2134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2135_: *mut LeanObject = core::ptr::null_mut();
    v_res_2135_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0(v_00_u03b2_2131_, v_inst_2132_, v_t_2133_, v_k_2134_);
    lean_dec(v_k_2134_);
    lean_dec(v_t_2133_);
    return v_res_2135_;
}
pub unsafe fn l_Lake_PartialBuildKey_fetchInCore(
    mut v_defaultPkg_2136_: *mut LeanObject,
    mut v_self_2137_: *mut LeanObject,
    mut v_a_2138_: *mut LeanObject,
    mut v_a_2139_: *mut LeanObject,
    mut v_a_2140_: *mut LeanObject,
    mut v_a_2141_: *mut LeanObject,
    mut v_a_2142_: *mut LeanObject,
    mut v_a_2143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2145_: u8 = 0;
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    v___x_2145_ = 1;
    lean_inc_ref(v_self_2137_);
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
    mut v_defaultPkg_2147_: *mut LeanObject,
    mut v_self_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
    mut v_a_2150_: *mut LeanObject,
    mut v_a_2151_: *mut LeanObject,
    mut v_a_2152_: *mut LeanObject,
    mut v_a_2153_: *mut LeanObject,
    mut v_a_2154_: *mut LeanObject,
    mut v_a_2155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2156_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2153_);
    lean_dec(v_a_2152_);
    lean_dec(v_a_2151_);
    lean_dec(v_a_2150_);
    return v_res_2156_;
}
pub unsafe fn l_Lake_PartialBuildKey_fetchIn(
    mut v_defaultPkg_2157_: *mut LeanObject,
    mut v_self_2158_: *mut LeanObject,
    mut v_a_2159_: *mut LeanObject,
    mut v_a_2160_: *mut LeanObject,
    mut v_a_2161_: *mut LeanObject,
    mut v_a_2162_: *mut LeanObject,
    mut v_a_2163_: *mut LeanObject,
    mut v_a_2164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2172_: u8 = 0;
    let mut v_snd_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2178_: u8 = 0;
    let mut v_a_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2183_: u8 = 0;
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2166_ = 1;
                lean_inc_ref(v_self_2158_);
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
                if lean_obj_tag(v___x_2167_) == 0 {
                    v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
                    v_a_2169_ = lean_ctor_get(v___x_2167_, 1);
                    v_isSharedCheck_2178_ = (!lean_is_exclusive(v___x_2167_)) as u8;
                    if v_isSharedCheck_2178_ == 0 {
                        v___x_2171_ = v___x_2167_;
                        v_isShared_2172_ = v_isSharedCheck_2178_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2169_);
                        lean_inc(v_a_2168_);
                        lean_dec(v___x_2167_);
                        v___x_2171_ = lean_box(0);
                        v_isShared_2172_ = v_isSharedCheck_2178_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2179_ = lean_ctor_get(v___x_2167_, 0);
                    v_a_2180_ = lean_ctor_get(v___x_2167_, 1);
                    v_isSharedCheck_2187_ = (!lean_is_exclusive(v___x_2167_)) as u8;
                    if v_isSharedCheck_2187_ == 0 {
                        v___x_2182_ = v___x_2167_;
                        v_isShared_2183_ = v_isSharedCheck_2187_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2180_);
                        lean_inc(v_a_2179_);
                        lean_dec(v___x_2167_);
                        v___x_2182_ = lean_box(0);
                        v_isShared_2183_ = v_isSharedCheck_2187_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2173_ = lean_ctor_get(v_a_2168_, 1);
                lean_inc(v_snd_2173_);
                lean_dec(v_a_2168_);
                v___x_2174_ = l_Lake_Job_toOpaque___redArg(v_snd_2173_);
                if v_isShared_2172_ == 0 {
                    lean_ctor_set(v___x_2171_, 0, v___x_2174_);
                    v___x_2176_ = v___x_2171_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
                    lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_a_2169_);
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
                    v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2179_);
                    lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_a_2180_);
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
    mut v_defaultPkg_2188_: *mut LeanObject,
    mut v_self_2189_: *mut LeanObject,
    mut v_a_2190_: *mut LeanObject,
    mut v_a_2191_: *mut LeanObject,
    mut v_a_2192_: *mut LeanObject,
    mut v_a_2193_: *mut LeanObject,
    mut v_a_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
    mut v_a_2196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2197_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2194_);
    lean_dec(v_a_2193_);
    lean_dec(v_a_2192_);
    lean_dec(v_a_2191_);
    return v_res_2197_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0(
    mut v_target_2198_: *mut LeanObject,
    mut v_kind_2199_: *mut LeanObject,
    mut v_facet_2200_: *mut LeanObject,
    mut v_data_2201_: *mut LeanObject,
    mut v___y_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
    mut v___y_2205_: *mut LeanObject,
    mut v___y_2206_: *mut LeanObject,
    mut v___y_2207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_log_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_action_2210_: u8 = 0;
    let mut v_wantsRebuild_2211_: u8 = 0;
    let mut v_trace_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buildTime_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2230_: u8 = 0;
    let mut v_a_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2235_: u8 = 0;
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_isSharedCheck_2243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_log_2209_ = lean_ctor_get(v___y_2207_, 0);
                v_action_2210_ = lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_wantsRebuild_2211_ = lean_ctor_get_uint8(
                    v___y_2207_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                );
                v_trace_2212_ = lean_ctor_get(v___y_2207_, 1);
                v_buildTime_2213_ = lean_ctor_get(v___y_2207_, 2);
                v_isSharedCheck_2243_ = (!lean_is_exclusive(v___y_2207_)) as u8;
                if v_isSharedCheck_2243_ == 0 {
                    v___x_2215_ = v___y_2207_;
                    v_isShared_2216_ = v_isSharedCheck_2243_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buildTime_2213_);
                    lean_inc(v_trace_2212_);
                    lean_inc(v_log_2209_);
                    lean_dec(v___y_2207_);
                    v___x_2215_ = lean_box(0);
                    v_isShared_2216_ = v_isSharedCheck_2243_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2217_ = lean_alloc_ctor(1, 4, (0) as u32);
                lean_ctor_set(v___x_2217_, 0, v_target_2198_);
                lean_ctor_set(v___x_2217_, 1, v_kind_2199_);
                lean_ctor_set(v___x_2217_, 2, v_data_2201_);
                lean_ctor_set(v___x_2217_, 3, v_facet_2200_);
                lean_inc_ref(v___y_2206_);
                lean_inc(v___y_2205_);
                lean_inc(v___y_2204_);
                lean_inc(v___y_2203_);
                v___x_2218_ = lean_apply_7(
                    v___y_2202_,
                    v___x_2217_,
                    v___y_2203_,
                    v___y_2204_,
                    v___y_2205_,
                    v___y_2206_,
                    v_log_2209_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2218_) == 0 {
                    v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
                    v_a_2220_ = lean_ctor_get(v___x_2218_, 1);
                    v_isSharedCheck_2230_ = (!lean_is_exclusive(v___x_2218_)) as u8;
                    if v_isSharedCheck_2230_ == 0 {
                        v___x_2222_ = v___x_2218_;
                        v_isShared_2223_ = v_isSharedCheck_2230_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2220_);
                        lean_inc(v_a_2219_);
                        lean_dec(v___x_2218_);
                        v___x_2222_ = lean_box(0);
                        v_isShared_2223_ = v_isSharedCheck_2230_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2231_ = lean_ctor_get(v___x_2218_, 0);
                    v_a_2232_ = lean_ctor_get(v___x_2218_, 1);
                    v_isSharedCheck_2242_ = (!lean_is_exclusive(v___x_2218_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2234_ = v___x_2218_;
                        v_isShared_2235_ = v_isSharedCheck_2242_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2232_);
                        lean_inc(v_a_2231_);
                        lean_dec(v___x_2218_);
                        v___x_2234_ = lean_box(0);
                        v_isShared_2235_ = v_isSharedCheck_2242_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2216_ == 0 {
                    lean_ctor_set(v___x_2215_, 0, v_a_2220_);
                    v___x_2225_ = v___x_2215_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2220_);
                    lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_trace_2212_);
                    lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_buildTime_2213_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2229_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_2210_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2229_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_2211_,
                    );
                    v___x_2225_ = v_reuseFailAlloc_2229_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2223_ == 0 {
                    lean_ctor_set(v___x_2222_, 1, v___x_2225_);
                    v___x_2227_ = v___x_2222_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2219_);
                    lean_ctor_set(v_reuseFailAlloc_2228_, 1, v___x_2225_);
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
                    lean_ctor_set(v___x_2215_, 0, v_a_2232_);
                    v___x_2237_ = v___x_2215_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 3, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2232_);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_trace_2212_);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_buildTime_2213_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2241_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_action_2210_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2241_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                        v_wantsRebuild_2211_,
                    );
                    v___x_2237_ = v_reuseFailAlloc_2241_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2235_ == 0 {
                    lean_ctor_set(v___x_2234_, 1, v___x_2237_);
                    v___x_2239_ = v___x_2234_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2231_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2237_);
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
    mut v_target_2244_: *mut LeanObject,
    mut v_kind_2245_: *mut LeanObject,
    mut v_facet_2246_: *mut LeanObject,
    mut v_data_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
    mut v___y_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
    mut v___y_2253_: *mut LeanObject,
    mut v___y_2254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2255_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v___y_2252_);
    lean_dec(v___y_2251_);
    lean_dec(v___y_2250_);
    lean_dec(v___y_2249_);
    return v_res_2255_;
}
pub unsafe fn l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore(
    mut v_root_2256_: *mut LeanObject,
    mut v_self_2257_: *mut LeanObject,
    mut v_a_2258_: *mut LeanObject,
    mut v_a_2259_: *mut LeanObject,
    mut v_a_2260_: *mut LeanObject,
    mut v_a_2261_: *mut LeanObject,
    mut v_a_2262_: *mut LeanObject,
    mut v_a_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: u8 = 0;
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_package_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_packageMap_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: u8 = 0;
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toContext_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_package_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2325_: u8 = 0;
    let mut v_packageMap_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: u8 = 0;
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: u8 = 0;
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: u8 = 0;
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u8 = 0;
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut v_toContext_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_package_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2386_: u8 = 0;
    let mut v_packageMap_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: u8 = 0;
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: u8 = 0;
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2411_: u8 = 0;
    let mut v_target_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facet_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2419_: u8 = 0;
    let mut v_kind_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: u8 = 0;
    let mut v_toContext_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facetConfigs_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_outKind_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u8 = 0;
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: u8 = 0;
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2265_ = l_Lake_instDataKindModule;
                match lean_obj_tag(v_self_2257_) {
                    0 => {
                        lean_dec_ref(v_a_2258_);
                        v_module_2266_ = lean_ctor_get(v_self_2257_, 0);
                        lean_inc_n(v_module_2266_, 2);
                        lean_dec_ref_known(v_self_2257_, 1);
                        v_toContext_2267_ = lean_ctor_get(v_a_2262_, 1);
                        v___x_2268_ =
                            l_Lake_Workspace_findModule_x3f(v_module_2266_, v_toContext_2267_);
                        if lean_obj_tag(v___x_2268_) == 1 {
                            lean_dec(v_module_2266_);
                            lean_dec_ref(v_root_2256_);
                            v_val_2269_ = lean_ctor_get(v___x_2268_, 0);
                            lean_inc(v_val_2269_);
                            lean_dec_ref_known(v___x_2268_, 1);
                            v___x_2270_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                            v___x_2271_ = 0;
                            v___x_2272_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                            v___x_2273_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2273_, 0, v_val_2269_);
                            lean_ctor_set(v___x_2273_, 1, v___x_2272_);
                            v___x_2274_ = lean_task_pure(v___x_2273_);
                            v___x_2275_ = lean_alloc_ctor(0, 3, (1) as u32);
                            lean_ctor_set(v___x_2275_, 0, v___x_2274_);
                            lean_ctor_set(v___x_2275_, 1, v___x_2265_);
                            lean_ctor_set(v___x_2275_, 2, v___x_2270_);
                            lean_ctor_set_uint8(
                                v___x_2275_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                                v___x_2271_,
                            );
                            v___x_2276_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2276_, 0, v___x_2275_);
                            lean_ctor_set(v___x_2276_, 1, v_a_2263_);
                            return v___x_2276_;
                        } else {
                            lean_dec(v___x_2268_);
                            v___x_2277_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                            v___x_2278_ = l_Lake_BuildKey_toString(v_root_2256_);
                            v___x_2279_ = lean_string_append(v___x_2277_, v___x_2278_);
                            lean_dec_ref(v___x_2278_);
                            v___x_2280_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5;
                            v___x_2281_ = lean_string_append(v___x_2279_, v___x_2280_);
                            v___x_2282_ = 1;
                            v___x_2283_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_module_2266_,
                                    v___x_2282_,
                                );
                            v___x_2284_ = lean_string_append(v___x_2281_, v___x_2283_);
                            lean_dec_ref(v___x_2283_);
                            v___x_2285_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                            v___x_2286_ = lean_string_append(v___x_2284_, v___x_2285_);
                            v___x_2287_ = 3;
                            v___x_2288_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_2288_, 0, v___x_2286_);
                            lean_ctor_set_uint8(
                                v___x_2288_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_2287_,
                            );
                            v___x_2289_ = lean_array_get_size(v_a_2263_);
                            v___x_2290_ = lean_array_push(v_a_2263_, v___x_2288_);
                            v___x_2291_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_2291_, 0, v___x_2289_);
                            lean_ctor_set(v___x_2291_, 1, v___x_2290_);
                            return v___x_2291_;
                        }
                    }
                    1 => {
                        lean_dec_ref(v_a_2258_);
                        v_toContext_2292_ = lean_ctor_get(v_a_2262_, 1);
                        v_package_2293_ = lean_ctor_get(v_self_2257_, 0);
                        lean_inc(v_package_2293_);
                        lean_dec_ref_known(v_self_2257_, 1);
                        v_packageMap_2294_ = lean_ctor_get(v_toContext_2292_, 5);
                        v___x_2295_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_2294_, v_package_2293_);
                        if lean_obj_tag(v___x_2295_) == 1 {
                            lean_dec(v_package_2293_);
                            lean_dec_ref(v_root_2256_);
                            v_val_2296_ = lean_ctor_get(v___x_2295_, 0);
                            lean_inc(v_val_2296_);
                            lean_dec_ref_known(v___x_2295_, 1);
                            v___x_2297_ = l_Lake_instDataKindPackage;
                            v___x_2298_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                            v___x_2299_ = 0;
                            v___x_2300_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                            v___x_2301_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2301_, 0, v_val_2296_);
                            lean_ctor_set(v___x_2301_, 1, v___x_2300_);
                            v___x_2302_ = lean_task_pure(v___x_2301_);
                            v___x_2303_ = lean_alloc_ctor(0, 3, (1) as u32);
                            lean_ctor_set(v___x_2303_, 0, v___x_2302_);
                            lean_ctor_set(v___x_2303_, 1, v___x_2297_);
                            lean_ctor_set(v___x_2303_, 2, v___x_2298_);
                            lean_ctor_set_uint8(
                                v___x_2303_,
                                (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                                v___x_2299_,
                            );
                            v___x_2304_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_2304_, 0, v___x_2303_);
                            lean_ctor_set(v___x_2304_, 1, v_a_2263_);
                            return v___x_2304_;
                        } else {
                            lean_dec(v___x_2295_);
                            v___x_2305_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                            v___x_2306_ = l_Lake_BuildKey_toString(v_root_2256_);
                            v___x_2307_ = lean_string_append(v___x_2305_, v___x_2306_);
                            lean_dec_ref(v___x_2306_);
                            v___x_2308_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                            v___x_2309_ = lean_string_append(v___x_2307_, v___x_2308_);
                            v___x_2310_ = 1;
                            v___x_2311_ =
                                l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                    v_package_2293_,
                                    v___x_2310_,
                                );
                            v___x_2312_ = lean_string_append(v___x_2309_, v___x_2311_);
                            lean_dec_ref(v___x_2311_);
                            v___x_2313_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                            v___x_2314_ = lean_string_append(v___x_2312_, v___x_2313_);
                            v___x_2315_ = 3;
                            v___x_2316_ = lean_alloc_ctor(0, 1, (1) as u32);
                            lean_ctor_set(v___x_2316_, 0, v___x_2314_);
                            lean_ctor_set_uint8(
                                v___x_2316_,
                                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                v___x_2315_,
                            );
                            v___x_2317_ = lean_array_get_size(v_a_2263_);
                            v___x_2318_ = lean_array_push(v_a_2263_, v___x_2316_);
                            v___x_2319_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_2319_, 0, v___x_2317_);
                            lean_ctor_set(v___x_2319_, 1, v___x_2318_);
                            return v___x_2319_;
                        }
                    }
                    2 => {
                        lean_dec_ref(v_a_2258_);
                        v_toContext_2320_ = lean_ctor_get(v_a_2262_, 1);
                        v_package_2321_ = lean_ctor_get(v_self_2257_, 0);
                        v_module_2322_ = lean_ctor_get(v_self_2257_, 1);
                        v_isSharedCheck_2380_ = (!lean_is_exclusive(v_self_2257_)) as u8;
                        if v_isSharedCheck_2380_ == 0 {
                            v___x_2324_ = v_self_2257_;
                            v_isShared_2325_ = v_isSharedCheck_2380_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_module_2322_);
                            lean_inc(v_package_2321_);
                            lean_dec(v_self_2257_);
                            v___x_2324_ = lean_box(0);
                            v_isShared_2325_ = v_isSharedCheck_2380_;
                            state = 1;
                            continue;
                        }
                    }
                    3 => {
                        v_toContext_2381_ = lean_ctor_get(v_a_2262_, 1);
                        v_package_2382_ = lean_ctor_get(v_self_2257_, 0);
                        v_target_2383_ = lean_ctor_get(v_self_2257_, 1);
                        v_isSharedCheck_2411_ = (!lean_is_exclusive(v_self_2257_)) as u8;
                        if v_isSharedCheck_2411_ == 0 {
                            v___x_2385_ = v_self_2257_;
                            v_isShared_2386_ = v_isSharedCheck_2411_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_target_2383_);
                            lean_inc(v_package_2382_);
                            lean_dec(v_self_2257_);
                            v___x_2385_ = lean_box(0);
                            v_isShared_2386_ = v_isSharedCheck_2411_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v_target_2412_ = lean_ctor_get(v_self_2257_, 0);
                        v_facet_2413_ = lean_ctor_get(v_self_2257_, 1);
                        lean_inc_ref(v_a_2258_);
                        lean_inc_ref(v_target_2412_);
                        lean_inc_ref(v_root_2256_);
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
                        if lean_obj_tag(v___x_2414_) == 0 {
                            v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
                            v_a_2416_ = lean_ctor_get(v___x_2414_, 1);
                            v_isSharedCheck_2463_ = (!lean_is_exclusive(v___x_2414_)) as u8;
                            if v_isSharedCheck_2463_ == 0 {
                                v___x_2418_ = v___x_2414_;
                                v_isShared_2419_ = v_isSharedCheck_2463_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_2416_);
                                lean_inc(v_a_2415_);
                                lean_dec(v___x_2414_);
                                v___x_2418_ = lean_box(0);
                                v_isShared_2419_ = v_isSharedCheck_2463_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_self_2257_, 2);
                            lean_dec_ref(v_a_2258_);
                            lean_dec_ref(v_root_2256_);
                            return v___x_2414_;
                        }
                    }
                }
            }
            1 => {
                v_packageMap_2326_ = lean_ctor_get(v_toContext_2320_, 5);
                v___x_2327_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_2326_, v_package_2321_);
                if lean_obj_tag(v___x_2327_) == 1 {
                    lean_dec(v_package_2321_);
                    v_val_2328_ = lean_ctor_get(v___x_2327_, 0);
                    lean_inc_n(v_val_2328_, 2);
                    lean_dec_ref_known(v___x_2327_, 1);
                    lean_inc(v_module_2322_);
                    v___x_2329_ = l_Lake_Package_findTargetModule_x3f(v_module_2322_, v_val_2328_);
                    if lean_obj_tag(v___x_2329_) == 1 {
                        lean_dec(v_val_2328_);
                        lean_dec(v_module_2322_);
                        lean_dec_ref(v_root_2256_);
                        v_val_2330_ = lean_ctor_get(v___x_2329_, 0);
                        lean_inc(v_val_2330_);
                        lean_dec_ref_known(v___x_2329_, 1);
                        v___x_2331_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__1;
                        v___x_2332_ = 0;
                        v___x_2333_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__4);
                        if v_isShared_2325_ == 0 {
                            lean_ctor_set_tag(v___x_2324_, 0);
                            lean_ctor_set(v___x_2324_, 1, v___x_2333_);
                            lean_ctor_set(v___x_2324_, 0, v_val_2330_);
                            v___x_2335_ = v___x_2324_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_val_2330_);
                            lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2333_);
                            v___x_2335_ = v_reuseFailAlloc_2339_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2329_);
                        v_baseName_2340_ = lean_ctor_get(v_val_2328_, 1);
                        lean_inc(v_baseName_2340_);
                        lean_dec(v_val_2328_);
                        v___x_2341_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_2342_ = l_Lake_BuildKey_toString(v_root_2256_);
                        v___x_2343_ = lean_string_append(v___x_2341_, v___x_2342_);
                        lean_dec_ref(v___x_2342_);
                        v___x_2344_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__5;
                        v___x_2345_ = lean_string_append(v___x_2343_, v___x_2344_);
                        v___x_2346_ = 1;
                        v___x_2347_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_module_2322_,
                                v___x_2346_,
                            );
                        v___x_2348_ = lean_string_append(v___x_2345_, v___x_2347_);
                        lean_dec_ref(v___x_2347_);
                        v___x_2349_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__7;
                        v___x_2350_ = lean_string_append(v___x_2348_, v___x_2349_);
                        v___x_2351_ = 0;
                        v___x_2352_ = l_Lean_Name_toString(v_baseName_2340_, v___x_2351_);
                        v___x_2353_ = lean_string_append(v___x_2350_, v___x_2352_);
                        lean_dec_ref(v___x_2352_);
                        v___x_2354_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                        v___x_2355_ = lean_string_append(v___x_2353_, v___x_2354_);
                        v___x_2356_ = 3;
                        v___x_2357_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_2357_, 0, v___x_2355_);
                        lean_ctor_set_uint8(
                            v___x_2357_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2356_,
                        );
                        v___x_2358_ = lean_array_get_size(v_a_2263_);
                        v___x_2359_ = lean_array_push(v_a_2263_, v___x_2357_);
                        if v_isShared_2325_ == 0 {
                            lean_ctor_set_tag(v___x_2324_, 1);
                            lean_ctor_set(v___x_2324_, 1, v___x_2359_);
                            lean_ctor_set(v___x_2324_, 0, v___x_2358_);
                            v___x_2361_ = v___x_2324_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2358_);
                            lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___x_2359_);
                            v___x_2361_ = v_reuseFailAlloc_2362_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2327_);
                    lean_dec(v_module_2322_);
                    v___x_2363_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_2364_ = l_Lake_BuildKey_toString(v_root_2256_);
                    v___x_2365_ = lean_string_append(v___x_2363_, v___x_2364_);
                    lean_dec_ref(v___x_2364_);
                    v___x_2366_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                    v___x_2367_ = lean_string_append(v___x_2365_, v___x_2366_);
                    v___x_2368_ = 1;
                    v___x_2369_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_package_2321_,
                        v___x_2368_,
                    );
                    v___x_2370_ = lean_string_append(v___x_2367_, v___x_2369_);
                    lean_dec_ref(v___x_2369_);
                    v___x_2371_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                    v___x_2372_ = lean_string_append(v___x_2370_, v___x_2371_);
                    v___x_2373_ = 3;
                    v___x_2374_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2374_, 0, v___x_2372_);
                    lean_ctor_set_uint8(
                        v___x_2374_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2373_,
                    );
                    v___x_2375_ = lean_array_get_size(v_a_2263_);
                    v___x_2376_ = lean_array_push(v_a_2263_, v___x_2374_);
                    if v_isShared_2325_ == 0 {
                        lean_ctor_set_tag(v___x_2324_, 1);
                        lean_ctor_set(v___x_2324_, 1, v___x_2376_);
                        lean_ctor_set(v___x_2324_, 0, v___x_2375_);
                        v___x_2378_ = v___x_2324_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2375_);
                        lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2376_);
                        v___x_2378_ = v_reuseFailAlloc_2379_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2336_ = lean_task_pure(v___x_2335_);
                v___x_2337_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_2337_, 0, v___x_2336_);
                lean_ctor_set(v___x_2337_, 1, v___x_2265_);
                lean_ctor_set(v___x_2337_, 2, v___x_2331_);
                lean_ctor_set_uint8(
                    v___x_2337_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2332_,
                );
                v___x_2338_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2338_, 0, v___x_2337_);
                lean_ctor_set(v___x_2338_, 1, v_a_2263_);
                return v___x_2338_;
            }
            3 => {
                return v___x_2361_;
            }
            4 => {
                return v___x_2378_;
            }
            5 => {
                v_packageMap_2387_ = lean_ctor_get(v_toContext_2381_, 5);
                v___x_2388_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00__private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_spec__0___redArg(v_packageMap_2387_, v_package_2382_);
                if lean_obj_tag(v___x_2388_) == 1 {
                    lean_dec(v_package_2382_);
                    lean_dec_ref(v_root_2256_);
                    v_val_2389_ = lean_ctor_get(v___x_2388_, 0);
                    lean_inc(v_val_2389_);
                    lean_dec_ref_known(v___x_2388_, 1);
                    if v_isShared_2386_ == 0 {
                        lean_ctor_set_tag(v___x_2385_, 0);
                        lean_ctor_set(v___x_2385_, 0, v_val_2389_);
                        v___x_2391_ = v___x_2385_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_val_2389_);
                        lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_target_2383_);
                        v___x_2391_ = v_reuseFailAlloc_2393_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2388_);
                    lean_dec(v_target_2383_);
                    lean_dec_ref(v_a_2258_);
                    v___x_2394_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_2395_ = l_Lake_BuildKey_toString(v_root_2256_);
                    v___x_2396_ = lean_string_append(v___x_2394_, v___x_2395_);
                    lean_dec_ref(v___x_2395_);
                    v___x_2397_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__1;
                    v___x_2398_ = lean_string_append(v___x_2396_, v___x_2397_);
                    v___x_2399_ = 1;
                    v___x_2400_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_package_2382_,
                        v___x_2399_,
                    );
                    v___x_2401_ = lean_string_append(v___x_2398_, v___x_2400_);
                    lean_dec_ref(v___x_2400_);
                    v___x_2402_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__2;
                    v___x_2403_ = lean_string_append(v___x_2401_, v___x_2402_);
                    v___x_2404_ = 3;
                    v___x_2405_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2405_, 0, v___x_2403_);
                    lean_ctor_set_uint8(
                        v___x_2405_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2404_,
                    );
                    v___x_2406_ = lean_array_get_size(v_a_2263_);
                    v___x_2407_ = lean_array_push(v_a_2263_, v___x_2405_);
                    if v_isShared_2386_ == 0 {
                        lean_ctor_set_tag(v___x_2385_, 1);
                        lean_ctor_set(v___x_2385_, 1, v___x_2407_);
                        lean_ctor_set(v___x_2385_, 0, v___x_2406_);
                        v___x_2409_ = v___x_2385_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2406_);
                        lean_ctor_set(v_reuseFailAlloc_2410_, 1, v___x_2407_);
                        v___x_2409_ = v_reuseFailAlloc_2410_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                lean_inc_ref(v_a_2262_);
                lean_inc(v_a_2261_);
                lean_inc(v_a_2260_);
                lean_inc(v_a_2259_);
                v___x_2392_ = lean_apply_7(
                    v_a_2258_,
                    v___x_2391_,
                    v_a_2259_,
                    v_a_2260_,
                    v_a_2261_,
                    v_a_2262_,
                    v_a_2263_,
                    lean_box(0),
                );
                return v___x_2392_;
            }
            7 => {
                return v___x_2409_;
            }
            8 => {
                v_kind_2420_ = lean_ctor_get(v_a_2415_, 1);
                v___x_2421_ = l_Lean_Name_isAnonymous(v_kind_2420_);
                if v___x_2421_ == 0 {
                    lean_inc(v_facet_2413_);
                    lean_inc_ref(v_target_2412_);
                    lean_dec_ref_known(v_self_2257_, 2);
                    v_toContext_2422_ = lean_ctor_get(v_a_2262_, 1);
                    v_facetConfigs_2423_ = lean_ctor_get(v_toContext_2422_, 6);
                    v___x_2424_ =
                        l_Lake_FacetConfigMap_get_x3f(v_facet_2413_, v_facetConfigs_2423_);
                    if lean_obj_tag(v___x_2424_) == 1 {
                        lean_dec_ref(v_root_2256_);
                        v_val_2425_ = lean_ctor_get(v___x_2424_, 0);
                        lean_inc(v_val_2425_);
                        lean_dec_ref_known(v___x_2424_, 1);
                        v_outKind_2426_ = lean_ctor_get(v_val_2425_, 2);
                        lean_inc(v_outKind_2426_);
                        lean_dec(v_val_2425_);
                        lean_inc(v_kind_2420_);
                        v___f_2427_ = lean_alloc_closure(l___private_Lake_Build_Target_Fetch_0__Lake_BuildKey_fetchCore___lam__0___boxed as *mut core::ffi::c_void, 11, 3);
                        lean_closure_set(v___f_2427_, 0, v_target_2412_);
                        lean_closure_set(v___f_2427_, 1, v_kind_2420_);
                        lean_closure_set(v___f_2427_, 2, v_facet_2413_);
                        v___x_2428_ = lean_unsigned_to_nat(0);
                        v___x_2429_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3), core::ptr::addr_of_mut!(l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3_once), _init_l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__3);
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
                            lean_ctor_set(v___x_2418_, 0, v___x_2430_);
                            v___x_2432_ = v___x_2418_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2433_, 0, v___x_2430_);
                            lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_a_2416_);
                            v___x_2432_ = v_reuseFailAlloc_2433_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2424_);
                        lean_dec(v_a_2415_);
                        lean_dec_ref(v_target_2412_);
                        lean_dec_ref(v_a_2258_);
                        v___x_2434_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                        v___x_2435_ = l_Lake_BuildKey_toString(v_root_2256_);
                        v___x_2436_ = lean_string_append(v___x_2434_, v___x_2435_);
                        lean_dec_ref(v___x_2435_);
                        v___x_2437_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__11;
                        v___x_2438_ = lean_string_append(v___x_2436_, v___x_2437_);
                        v___x_2439_ = 1;
                        v___x_2440_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_facet_2413_,
                                v___x_2439_,
                            );
                        v___x_2441_ = lean_string_append(v___x_2438_, v___x_2440_);
                        lean_dec_ref(v___x_2440_);
                        v___x_2442_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                        v___x_2443_ = lean_string_append(v___x_2441_, v___x_2442_);
                        v___x_2444_ = 3;
                        v___x_2445_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_2445_, 0, v___x_2443_);
                        lean_ctor_set_uint8(
                            v___x_2445_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_2444_,
                        );
                        v___x_2446_ = lean_array_get_size(v_a_2416_);
                        v___x_2447_ = lean_array_push(v_a_2416_, v___x_2445_);
                        if v_isShared_2419_ == 0 {
                            lean_ctor_set_tag(v___x_2418_, 1);
                            lean_ctor_set(v___x_2418_, 1, v___x_2447_);
                            lean_ctor_set(v___x_2418_, 0, v___x_2446_);
                            v___x_2449_ = v___x_2418_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2446_);
                            lean_ctor_set(v_reuseFailAlloc_2450_, 1, v___x_2447_);
                            v___x_2449_ = v_reuseFailAlloc_2450_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_2415_);
                    lean_dec_ref(v_a_2258_);
                    lean_dec_ref(v_root_2256_);
                    v___x_2451_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux_resolveTargetPackageD___redArg___closed__0;
                    v___x_2452_ = l_Lake_BuildKey_toString(v_self_2257_);
                    v___x_2453_ = lean_string_append(v___x_2451_, v___x_2452_);
                    lean_dec_ref(v___x_2452_);
                    v___x_2454_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__13;
                    v___x_2455_ = lean_string_append(v___x_2453_, v___x_2454_);
                    v___x_2456_ = 3;
                    v___x_2457_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_2457_, 0, v___x_2455_);
                    lean_ctor_set_uint8(
                        v___x_2457_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_2456_,
                    );
                    v___x_2458_ = lean_array_get_size(v_a_2416_);
                    v___x_2459_ = lean_array_push(v_a_2416_, v___x_2457_);
                    if v_isShared_2419_ == 0 {
                        lean_ctor_set_tag(v___x_2418_, 1);
                        lean_ctor_set(v___x_2418_, 1, v___x_2459_);
                        lean_ctor_set(v___x_2418_, 0, v___x_2458_);
                        v___x_2461_ = v___x_2418_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2458_);
                        lean_ctor_set(v_reuseFailAlloc_2462_, 1, v___x_2459_);
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
    mut v_root_2464_: *mut LeanObject,
    mut v_self_2465_: *mut LeanObject,
    mut v_a_2466_: *mut LeanObject,
    mut v_a_2467_: *mut LeanObject,
    mut v_a_2468_: *mut LeanObject,
    mut v_a_2469_: *mut LeanObject,
    mut v_a_2470_: *mut LeanObject,
    mut v_a_2471_: *mut LeanObject,
    mut v_a_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2473_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2470_);
    lean_dec(v_a_2469_);
    lean_dec(v_a_2468_);
    lean_dec(v_a_2467_);
    return v_res_2473_;
}
pub unsafe fn l_Lake_BuildKey_fetch___redArg(
    mut v_self_2474_: *mut LeanObject,
    mut v_a_2475_: *mut LeanObject,
    mut v_a_2476_: *mut LeanObject,
    mut v_a_2477_: *mut LeanObject,
    mut v_a_2478_: *mut LeanObject,
    mut v_a_2479_: *mut LeanObject,
    mut v_a_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_self_2474_);
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
    mut v_self_2483_: *mut LeanObject,
    mut v_a_2484_: *mut LeanObject,
    mut v_a_2485_: *mut LeanObject,
    mut v_a_2486_: *mut LeanObject,
    mut v_a_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2491_: *mut LeanObject = core::ptr::null_mut();
    v_res_2491_ = l_Lake_BuildKey_fetch___redArg(
        v_self_2483_,
        v_a_2484_,
        v_a_2485_,
        v_a_2486_,
        v_a_2487_,
        v_a_2488_,
        v_a_2489_,
    );
    lean_dec_ref(v_a_2488_);
    lean_dec(v_a_2487_);
    lean_dec(v_a_2486_);
    lean_dec(v_a_2485_);
    return v_res_2491_;
}
pub unsafe fn l_Lake_BuildKey_fetch(
    mut v_00_u03b1_2492_: *mut LeanObject,
    mut v_self_2493_: *mut LeanObject,
    mut v_inst_2494_: *mut LeanObject,
    mut v_a_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
    mut v_a_2499_: *mut LeanObject,
    mut v_a_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_self_2493_);
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
    mut v_00_u03b1_2503_: *mut LeanObject,
    mut v_self_2504_: *mut LeanObject,
    mut v_inst_2505_: *mut LeanObject,
    mut v_a_2506_: *mut LeanObject,
    mut v_a_2507_: *mut LeanObject,
    mut v_a_2508_: *mut LeanObject,
    mut v_a_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2513_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2510_);
    lean_dec(v_a_2509_);
    lean_dec(v_a_2508_);
    lean_dec(v_a_2507_);
    return v_res_2513_;
}
pub unsafe fn l_Lake_Target_fetchIn___redArg(
    mut v_inst_2518_: *mut LeanObject,
    mut v_defaultPkg_2519_: *mut LeanObject,
    mut v_self_2520_: *mut LeanObject,
    mut v_a_2521_: *mut LeanObject,
    mut v_a_2522_: *mut LeanObject,
    mut v_a_2523_: *mut LeanObject,
    mut v_a_2524_: *mut LeanObject,
    mut v_a_2525_: *mut LeanObject,
    mut v_a_2526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2534_: u8 = 0;
    let mut v___y_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2557_: u8 = 0;
    let mut v_kind_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: u8 = 0;
    let mut v___x_2560_: u8 = 0;
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2569_: u8 = 0;
    let mut v_unused_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2571_: u8 = 0;
    let mut v_a_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2576_: u8 = 0;
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2528_ = 1;
                lean_inc_ref_n(v_self_2520_, 2);
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
                if lean_obj_tag(v___x_2529_) == 0 {
                    v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
                    v_a_2531_ = lean_ctor_get(v___x_2529_, 1);
                    v_isSharedCheck_2571_ = (!lean_is_exclusive(v___x_2529_)) as u8;
                    if v_isSharedCheck_2571_ == 0 {
                        v___x_2533_ = v___x_2529_;
                        v_isShared_2534_ = v_isSharedCheck_2571_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2531_);
                        lean_inc(v_a_2530_);
                        lean_dec(v___x_2529_);
                        v___x_2533_ = lean_box(0);
                        v_isShared_2534_ = v_isSharedCheck_2571_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_self_2520_);
                    lean_dec(v_inst_2518_);
                    v_a_2572_ = lean_ctor_get(v___x_2529_, 0);
                    v_a_2573_ = lean_ctor_get(v___x_2529_, 1);
                    v_isSharedCheck_2580_ = (!lean_is_exclusive(v___x_2529_)) as u8;
                    if v_isSharedCheck_2580_ == 0 {
                        v___x_2575_ = v___x_2529_;
                        v_isShared_2576_ = v_isSharedCheck_2580_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2573_);
                        lean_inc(v_a_2572_);
                        lean_dec(v___x_2529_);
                        v___x_2575_ = lean_box(0);
                        v_isShared_2576_ = v_isSharedCheck_2580_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2554_ = lean_ctor_get(v_a_2530_, 1);
                v_isSharedCheck_2569_ = (!lean_is_exclusive(v_a_2530_)) as u8;
                if v_isSharedCheck_2569_ == 0 {
                    v_unused_2570_ = lean_ctor_get(v_a_2530_, 0);
                    lean_dec(v_unused_2570_);
                    v___x_2556_ = v_a_2530_;
                    v_isShared_2557_ = v_isSharedCheck_2569_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_2554_);
                    lean_dec(v_a_2530_);
                    v___x_2556_ = lean_box(0);
                    v_isShared_2557_ = v_isSharedCheck_2569_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2537_ = l_Lake_Target_fetchIn___redArg___closed__0;
                v___x_2538_ = l_Lake_PartialBuildKey_toString(v_self_2520_);
                v___x_2539_ = lean_string_append(v___x_2537_, v___x_2538_);
                lean_dec_ref(v___x_2538_);
                v___x_2540_ = l_Lake_Target_fetchIn___redArg___closed__1;
                v___x_2541_ = lean_string_append(v___x_2539_, v___x_2540_);
                v___x_2542_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_inst_2518_,
                    v___x_2528_,
                );
                v___x_2543_ = lean_string_append(v___x_2541_, v___x_2542_);
                lean_dec_ref(v___x_2542_);
                v___x_2544_ = l_Lake_Target_fetchIn___redArg___closed__2;
                v___x_2545_ = lean_string_append(v___x_2543_, v___x_2544_);
                v___x_2546_ = lean_string_append(v___x_2545_, v___y_2536_);
                lean_dec_ref(v___y_2536_);
                v___x_2547_ = 3;
                v___x_2548_ = lean_alloc_ctor(0, 1, (1) as u32);
                lean_ctor_set(v___x_2548_, 0, v___x_2546_);
                lean_ctor_set_uint8(
                    v___x_2548_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2547_,
                );
                v___x_2549_ = lean_array_get_size(v_a_2531_);
                v___x_2550_ = lean_array_push(v_a_2531_, v___x_2548_);
                if v_isShared_2534_ == 0 {
                    lean_ctor_set_tag(v___x_2533_, 1);
                    lean_ctor_set(v___x_2533_, 1, v___x_2550_);
                    lean_ctor_set(v___x_2533_, 0, v___x_2549_);
                    v___x_2552_ = v___x_2533_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2549_);
                    lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2550_);
                    v___x_2552_ = v_reuseFailAlloc_2553_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2552_;
            }
            4 => {
                v_kind_2558_ = lean_ctor_get(v_snd_2554_, 1);
                v___x_2559_ = lean_name_eq(v_kind_2558_, v_inst_2518_);
                if v___x_2559_ == 0 {
                    lean_inc(v_kind_2558_);
                    lean_del_object(v___x_2556_);
                    lean_dec(v_snd_2554_);
                    v___x_2560_ = l_Lean_Name_isAnonymous(v_kind_2558_);
                    if v___x_2560_ == 0 {
                        v___x_2561_ = l___private_Lake_Build_Target_Fetch_0__Lake_PartialBuildKey_fetchInCoreAux___closed__8;
                        v___x_2562_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_kind_2558_,
                                v___x_2528_,
                            );
                        v___x_2563_ = lean_string_append(v___x_2561_, v___x_2562_);
                        lean_dec_ref(v___x_2562_);
                        v___x_2564_ = lean_string_append(v___x_2563_, v___x_2561_);
                        v___y_2536_ = v___x_2564_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_kind_2558_);
                        v___x_2565_ = l_Lake_Target_fetchIn___redArg___closed__3;
                        v___y_2536_ = v___x_2565_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2533_);
                    lean_dec_ref(v_self_2520_);
                    lean_dec(v_inst_2518_);
                    if v_isShared_2557_ == 0 {
                        lean_ctor_set(v___x_2556_, 1, v_a_2531_);
                        lean_ctor_set(v___x_2556_, 0, v_snd_2554_);
                        v___x_2567_ = v___x_2556_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_snd_2554_);
                        lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_a_2531_);
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
                    v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2572_);
                    lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_a_2573_);
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
    mut v_inst_2581_: *mut LeanObject,
    mut v_defaultPkg_2582_: *mut LeanObject,
    mut v_self_2583_: *mut LeanObject,
    mut v_a_2584_: *mut LeanObject,
    mut v_a_2585_: *mut LeanObject,
    mut v_a_2586_: *mut LeanObject,
    mut v_a_2587_: *mut LeanObject,
    mut v_a_2588_: *mut LeanObject,
    mut v_a_2589_: *mut LeanObject,
    mut v_a_2590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2591_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2588_);
    lean_dec(v_a_2587_);
    lean_dec(v_a_2586_);
    lean_dec(v_a_2585_);
    return v_res_2591_;
}
pub unsafe fn l_Lake_Target_fetchIn(
    mut v_00_u03b1_2592_: *mut LeanObject,
    mut v_inst_2593_: *mut LeanObject,
    mut v_defaultPkg_2594_: *mut LeanObject,
    mut v_self_2595_: *mut LeanObject,
    mut v_a_2596_: *mut LeanObject,
    mut v_a_2597_: *mut LeanObject,
    mut v_a_2598_: *mut LeanObject,
    mut v_a_2599_: *mut LeanObject,
    mut v_a_2600_: *mut LeanObject,
    mut v_a_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2604_: *mut LeanObject,
    mut v_inst_2605_: *mut LeanObject,
    mut v_defaultPkg_2606_: *mut LeanObject,
    mut v_self_2607_: *mut LeanObject,
    mut v_a_2608_: *mut LeanObject,
    mut v_a_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
    mut v_a_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2615_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2612_);
    lean_dec(v_a_2611_);
    lean_dec(v_a_2610_);
    lean_dec(v_a_2609_);
    return v_res_2615_;
}
pub unsafe fn l_Lake_TargetArray_fetchIn___redArg___lam__0(
    mut v_inst_2616_: *mut LeanObject,
    mut v_defaultPkg_2617_: *mut LeanObject,
    mut v_x_2618_: *mut LeanObject,
    mut v___y_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_2627_: *mut LeanObject,
    mut v_defaultPkg_2628_: *mut LeanObject,
    mut v_x_2629_: *mut LeanObject,
    mut v___y_2630_: *mut LeanObject,
    mut v___y_2631_: *mut LeanObject,
    mut v___y_2632_: *mut LeanObject,
    mut v___y_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
    mut v___y_2635_: *mut LeanObject,
    mut v___y_2636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2637_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v___y_2634_);
    lean_dec(v___y_2633_);
    lean_dec(v___y_2632_);
    lean_dec(v___y_2631_);
    return v_res_2637_;
}
pub unsafe fn l_Lake_TargetArray_fetchIn___redArg(
    mut v_inst_2638_: *mut LeanObject,
    mut v_defaultPkg_2639_: *mut LeanObject,
    mut v_self_2640_: *mut LeanObject,
    mut v_traceCaption_2641_: *mut LeanObject,
    mut v_a_2642_: *mut LeanObject,
    mut v_a_2643_: *mut LeanObject,
    mut v_a_2644_: *mut LeanObject,
    mut v_a_2645_: *mut LeanObject,
    mut v_a_2646_: *mut LeanObject,
    mut v_a_2647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2668_: usize = 0;
    let mut v___x_2669_: usize = 0;
    let mut v___x_521__overap_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2676_: u8 = 0;
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2681_: u8 = 0;
    let mut v_a_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2686_: u8 = 0;
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2690_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2649_ = l_instMonadBaseIO;
                v_toApplicative_2650_ = lean_ctor_get(v___x_2649_, 0);
                v_toBind_2651_ = lean_ctor_get(v___x_2649_, 1);
                v_toFunctor_2652_ = lean_ctor_get(v_toApplicative_2650_, 0);
                v_toPure_2653_ = lean_ctor_get(v_toApplicative_2650_, 1);
                v___f_2654_ = lean_alloc_closure(
                    l_Lake_TargetArray_fetchIn___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    10,
                    2,
                );
                lean_closure_set(v___f_2654_, 0, v_inst_2638_);
                lean_closure_set(v___f_2654_, 1, v_defaultPkg_2639_);
                lean_inc_n(v_toBind_2651_, 3);
                lean_inc_n(v_toPure_2653_, 5);
                v___f_2655_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_2655_, 0, v_toPure_2653_);
                lean_closure_set(v___f_2655_, 1, v_toBind_2651_);
                v___f_2656_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_2656_, 0, v_toPure_2653_);
                lean_closure_set(v___f_2656_, 1, v_toBind_2651_);
                lean_inc_ref(v___f_2655_);
                v___f_2657_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_2657_, 0, v_toPure_2653_);
                lean_closure_set(v___f_2657_, 1, v___f_2655_);
                lean_inc_ref_n(v_toFunctor_2652_, 2);
                v___f_2658_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                lean_closure_set(v___f_2658_, 0, v_toFunctor_2652_);
                lean_closure_set(v___f_2658_, 1, v_toPure_2653_);
                lean_closure_set(v___f_2658_, 2, v_toBind_2651_);
                v___x_2659_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_2652_);
                v___f_2660_ = lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_2660_, 0, v_toPure_2653_);
                v___x_2661_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2661_, 0, v___x_2659_);
                lean_ctor_set(v___x_2661_, 1, v___f_2660_);
                lean_ctor_set(v___x_2661_, 2, v___f_2658_);
                lean_ctor_set(v___x_2661_, 3, v___f_2657_);
                lean_ctor_set(v___x_2661_, 4, v___f_2656_);
                v___x_2662_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2662_, 0, v___x_2661_);
                lean_ctor_set(v___x_2662_, 1, v___f_2655_);
                v___x_2663_ = l_ReaderT_instMonad___redArg(v___x_2662_);
                v___x_2664_ = l_StateRefT_x27_instMonad___redArg(v___x_2663_);
                v___x_2665_ = l_ReaderT_instMonad___redArg(v___x_2664_);
                v___x_2666_ = l_ReaderT_instMonad___redArg(v___x_2665_);
                v___x_2667_ = l_Lake_EquipT_instMonad___redArg(v___x_2666_);
                v_sz_2668_ = lean_array_size(v_self_2640_);
                v___x_2669_ = 0usize;
                v___x_521__overap_2670_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v___x_2667_,
                    v___f_2654_,
                    v_sz_2668_,
                    v___x_2669_,
                    v_self_2640_,
                );
                lean_inc_ref(v_a_2646_);
                lean_inc(v_a_2645_);
                lean_inc(v_a_2644_);
                lean_inc(v_a_2643_);
                v___x_2671_ = lean_apply_7(
                    v___x_521__overap_2670_,
                    v_a_2642_,
                    v_a_2643_,
                    v_a_2644_,
                    v_a_2645_,
                    v_a_2646_,
                    v_a_2647_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2671_) == 0 {
                    v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
                    v_a_2673_ = lean_ctor_get(v___x_2671_, 1);
                    v_isSharedCheck_2681_ = (!lean_is_exclusive(v___x_2671_)) as u8;
                    if v_isSharedCheck_2681_ == 0 {
                        v___x_2675_ = v___x_2671_;
                        v_isShared_2676_ = v_isSharedCheck_2681_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2673_);
                        lean_inc(v_a_2672_);
                        lean_dec(v___x_2671_);
                        v___x_2675_ = lean_box(0);
                        v_isShared_2676_ = v_isSharedCheck_2681_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_traceCaption_2641_);
                    v_a_2682_ = lean_ctor_get(v___x_2671_, 0);
                    v_a_2683_ = lean_ctor_get(v___x_2671_, 1);
                    v_isSharedCheck_2690_ = (!lean_is_exclusive(v___x_2671_)) as u8;
                    if v_isSharedCheck_2690_ == 0 {
                        v___x_2685_ = v___x_2671_;
                        v_isShared_2686_ = v_isSharedCheck_2690_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2683_);
                        lean_inc(v_a_2682_);
                        lean_dec(v___x_2671_);
                        v___x_2685_ = lean_box(0);
                        v_isShared_2686_ = v_isSharedCheck_2690_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2677_ = l_Lake_Job_collectArray___redArg(v_a_2672_, v_traceCaption_2641_);
                lean_dec(v_a_2672_);
                if v_isShared_2676_ == 0 {
                    lean_ctor_set(v___x_2675_, 0, v___x_2677_);
                    v___x_2679_ = v___x_2675_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
                    lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_a_2673_);
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
                    v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2682_);
                    lean_ctor_set(v_reuseFailAlloc_2689_, 1, v_a_2683_);
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
    mut v_inst_2691_: *mut LeanObject,
    mut v_defaultPkg_2692_: *mut LeanObject,
    mut v_self_2693_: *mut LeanObject,
    mut v_traceCaption_2694_: *mut LeanObject,
    mut v_a_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
    mut v_a_2699_: *mut LeanObject,
    mut v_a_2700_: *mut LeanObject,
    mut v_a_2701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2702_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2699_);
    lean_dec(v_a_2698_);
    lean_dec(v_a_2697_);
    lean_dec(v_a_2696_);
    return v_res_2702_;
}
pub unsafe fn l_Lake_TargetArray_fetchIn(
    mut v_00_u03b1_2703_: *mut LeanObject,
    mut v_inst_2704_: *mut LeanObject,
    mut v_defaultPkg_2705_: *mut LeanObject,
    mut v_self_2706_: *mut LeanObject,
    mut v_traceCaption_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
    mut v_a_2709_: *mut LeanObject,
    mut v_a_2710_: *mut LeanObject,
    mut v_a_2711_: *mut LeanObject,
    mut v_a_2712_: *mut LeanObject,
    mut v_a_2713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2716_: *mut LeanObject,
    mut v_inst_2717_: *mut LeanObject,
    mut v_defaultPkg_2718_: *mut LeanObject,
    mut v_self_2719_: *mut LeanObject,
    mut v_traceCaption_2720_: *mut LeanObject,
    mut v_a_2721_: *mut LeanObject,
    mut v_a_2722_: *mut LeanObject,
    mut v_a_2723_: *mut LeanObject,
    mut v_a_2724_: *mut LeanObject,
    mut v_a_2725_: *mut LeanObject,
    mut v_a_2726_: *mut LeanObject,
    mut v_a_2727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2728_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_2725_);
    lean_dec(v_a_2724_);
    lean_dec(v_a_2723_);
    lean_dec(v_a_2722_);
    return v_res_2728_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Target_Fetch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Job_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Key(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Target_Fetch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Target_Fetch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Infos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Job_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Build_Key(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Target_Fetch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Target_Fetch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Build_Target_Fetch(builtin);
}
